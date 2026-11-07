# SW-1808: review of the kept search session (SW-1798)

An independent review of SW-1798 (merge `41ae3d7fd`, commit `d3303e1d4`),
done by reading the code only. Nothing was built or run. Where a question
can only be settled by running something, the test to run is written out.

The change: a search worker thread keeps one session with the library
loaded (`WARM`, a thread-local in `crates/lsp/src/lib.rs`), marked just
after the load. It is rewound to that mark after every project search:
members completion, `contextAt`, split patterns and code actions. Files on
their own still get a fresh session per request, and so does the browser.

## Verdict

**I found no state that a rewind leaves behind and that changes an answer**
of any of the four request kinds today, over any number of requests, edits
or project switches. Everything a request sets that a rewind doesn't
restore is set again at the start of the next request, or never read
again.

The differences from a fresh session are memory growth, behaviour after a
panic, and robustness against future changes:

- Two lists grow with every request and are never cut back: the
  counterexample search logs and the kernel's `apart_sets`. Both are slow
  leaks (finding 1, 2).
- A panic in a search still kills the worker thread natively. The new
  code's "a panic leaves none behind" only matters if the thread survives,
  and it doesn't. This was true before SW-1798 (finding 3).
- `Machine::reset` doesn't put the kernel's glue and erasure modes back.
  Harmless now, because no catch of a panic is reachable from these paths.
  It becomes a wrong answer that persists for the rest of the session if
  one is ever added (finding 4).
- The session's key is incomplete in principle (finding 5). The answers'
  documentation overstates cancellation (finding 6). The known difference
  in navigation modes for code actions moves code actions to another
  check-cache key (finding 7).
- The kept session is dropped while the thread's other thread-locals are
  being destroyed (finding 8).

The new test checks the main claim on one project and one text family. It
would catch none of findings 1–8 (see "The test").

**Recommendation:** keep SW-1798. File findings 1, 2 and 3 as small
tickets. Make findings 4 and 8 one-line hardening fixes. Add the
driver-level differential test below (D2583).

## Findings

Severities: **wrong answer**, **leak** (memory that grows without bound),
**cosmetic** (documentation, naming, perf or hardening, with no wrong
answer now).

### 1. Counterexample search logs grow with every request (leak)

`crates/elab/src/counterexample/mod.rs:276` pushes a `SearchLog` onto
`present.counterexample_log` each time a theorem fails and a counterexample
search runs. `crates/elab/src/state/presentation.rs:47-62` says "only grows;
a rewind leaves it".

A probe checks the probed namespace and doesn't replay it
(`cache/mod.rs:617`, `probes_one_of`), so every `contextAt` or completion
in a namespace with failing theorems runs their counterexample searches
again. In a fresh session the logs died with the session. In the kept
session they pile up.

**Scenario:** a user is writing proofs in a file with five failing theorems.
The extension asks for `contextAt` as the cursor moves and for completion
after each `.`. That is thousands of requests in an afternoon, each adding
five logs (strings and vectors, around a kilobyte each), so tens of MB on a
session that is already 0.45 GB. Nothing reads them except `.last()`, right
after the push (`module.rs:663`).

**Fix, either or both:**

- (a) Set `options.no_counterexamples = true` in the probe sessions and
  the kept session. Their answers never include diagnostics, and the
  option isn't part of the cache key (`state/options.rs:110`), so the
  cache is unaffected. This also saves each probe the counterexample
  searches' time: up to their time limit per failing theorem, on every
  request, before and after SW-1798. Code actions do read diagnostics, but
  they only count errors, and the note is attached to an error that is
  there anyway. Check that before turning it off for code actions too.
- (b) Have `Presentation::mark` record the log's length and `rewind`
  truncate it. "Kept: the log of searches already run" serves the
  `search` CLI's report, which never rewinds.

**Test:** in the driver test below, after the warm-up, record
`elab.present.counterexample_log.borrow().len()`. Repeat a `contextAt`
in a namespace with a failing theorem 50 times, then assert the length
hasn't changed.

### 2. `Machine::apart_sets` grows with every request (leak, small)

`crates/core/src/value.rs:203`: `Apart::new` pushes a new set every time
with no deduplication. It is called from the kernel's checker
(`core/src/check.rs:1303`) and the elaborator (`elab/src/lib.rs:4932`) for
the default arm of every number case they go into.
`crates/core/src/machine.rs:44-51` keeps the list on a rewind, by design:
a value may still hold an index into it.

**Scenario:** a project whose probed namespace (or a namespace it uses, if
that one misses the cache) has number matches with a `_` arm. Every
request adds one `Rc<[BigUint]>` for each such arm checked. Each is small,
but there is no bound. The ids don't appear in printed output or cache
entries (`Apart` is only in `Value`, not `Term`), so their drift changes
no answer.

**Fix:**

- Intern the sets: look up an equal set before pushing (a `HashMap<Rc<[BigUint]>, u32>`
  beside the vector). This bounds the list by the distinct sets ever seen.
- Or cut the list at a rewind. A rewind already drops every value made
  since the mark (the caches are cut or emptied, and the inference state
  is emptied), so that may be safe, but it needs Opus review: it is kernel
  state.

**Test:** read `machine.apart_sets.borrow().len()` before and after 50
repeated probes of a namespace containing `match n | 0 => … | _ => …`,
and assert it is unchanged (with interning).

### 3. A panic in a search kills the worker natively, and searches stop for the session (wrong answer, from before SW-1798)

`crates/lsp/src/lib.rs:603-613` (`search_worker`) and `616-646`
(`run_search`) have no `catch_unwind`. The new comment at `lib.rs:2982`
says the session is "taken out while in use, so that a panic leaves none
behind". That is true, but the panic then unwinds out of `search_worker`
and ends the thread:

- The request in flight is never answered.
- `searches.running` stays incremented.
- With the default single worker (`lib.rs:127`), every later search is
  answered null immediately, because the send fails once no receiver is
  left (`lib.rs:987`).

So searches stop for the rest of the editor session. Before SW-1798 this
was the same, so it isn't a regression. But the kept session's design only
makes sense if the thread survives the panic.

**Fix:**

- Wrap `(job.search).run(...)` in `run_search` in
  `std::panic::catch_unwind(AssertUnwindSafe(..))` and answer null on a
  panic. The `take()` in `with_project_session` then does what its
  comment says: the half-used session is dropped during unwinding, and the
  next request builds a new one.
- Decrement `running` on both paths.
- In the browser a panic aborts the instance anyway.

**Test:** a test-only `SearchKind`, or an environment hook that panics in
`Search::run`, then a second search that must get a real answer. That
needs either a test seam or a known panicking input; D2584 asks whether
it's worth one.

### 4. `Machine::reset` leaves glue and erasure as they are (cosmetic now; wrong answer if a panic is ever caught mid-request)

`crates/core/src/machine.rs:51-54` resets the budget and the transparency
set. It doesn't reset `glue` (`Cell<bool>`) or the erasure switches. These
are set by save-and-restore pairs with no guard
(`core/src/check.rs:1782/1784`, `reference.rs:973/995`, `inert.rs:90/111`,
`value.rs:2010/2012`; `machine.rs:63-79` says "nothing needs a guard"
because the kernel returns errors rather than unwinding).

The one `catch_unwind` inside the elaborator, `elab/src/search.rs:1402`
(the `search` command's `search_one`), isn't reachable from
`search_at_project` or the probes. So today a panic always drops the
session.

If finding 3 is fixed by catching the panic around `Search::run`, this
stays safe: the session is still dropped. But if a catch is ever added
*inside* a request (as `search.rs:1402` does for the `search` command),
a panic between `glue.replace(true)` and `glue.set(was)` leaves glue on.
In a fresh session that lasted one request. In the kept session it lasts
until the thread ends, and every later elaboration outside the kernel
would run glued. That would change printed types (folded calls), and so
the answers.

**Fix:** have `Machine::reset` also set `glue` to false and restore
erasure to "off". At a rewind's point (between operations) both must
be off by the module's own rule. This is a kernel-adjacent change, so it
goes to Opus (D2506).

**Test:** none needed beyond an assertion in `Kernel::rewind`
(`debug_assert!(!machine.glue.get())`) that would have caught a leaked
mode in the existing rewind tests.

### 5. The session key is `(stack, bundle address)` (cosmetic)

`lib.rs:2978-2981`. That is everything `search_session` reads today:
`library_session` / `session_for` use only `stack` and `library`. Std is
read once per process (`elab/src/std_dir.rs:72-88`, a `OnceLock`), and
`Options::library` is a `OnceLock` that only goes from empty to set
(`lib.rs:104`), which changes the key. So the key is complete today.

Two weaknesses:

- (a) A pointer as identity: a bundle dropped and another allocated at
  the same address on the same thread would match. In the server that
  can't happen, since there is one bundle per process. In tests that make
  several `Options` with different bundles on one thread, it could.
- (b) Anything added to `search_session` later (a limit, a test switch,
  `no_counterexamples` from finding 1) must also go into the key, and
  nothing says so.

**Fix:**

- Build the warm session's key from the same function that configures the
  session, for example a small `SearchConfig` that both makes the session
  and is compared.
- Compare the bundle with `Arc::ptr_eq` against an `Arc` the `Warm` holds.
  Holding it also keeps the address from being reused.

### 6. "The project path honours" cancellation: it doesn't (cosmetic, from before SW-1798)

`lib.rs:572` says the cancel flag "stops a search that is running (the
project path honours it)". The searches only install the flag
(`share_cancel_flag`, `lib.rs:2973, 2992, 3007, 2914, 3054`). The budget
only looks at it while `watching` is set (`core/src/budget.rs:469-500`),
and the only place that sets `watching` is `Session::cancellable_at`
(`driver/src/rewind.rs:103`), which no search path calls.

So a cancelled search runs to the end, or to its own time limit for code
actions, and then `searched` answers null. Nothing is left half-rewound,
because nothing stops part way.

If cancellation is ever wired in by wrapping `f` in `cancellable`, the
kept session copes. `cancellable` takes and releases a nested mark, and
`machine.reset()` in the outer rewind clears `cancelled`
(`budget.rs:513`).

**Fix:** correct the comment, or wire it in: wrap the body of `f` in
`session.cancellable(..)` and treat `Err(Cancelled)` as null. Wiring it
in is worth more now: a single worker held by a stale multi-second code
action delays every completion behind it.

### 7. The known navigation-mode difference moves code actions to another cache key (cosmetic)

What each session does:

- **Fresh code-action session without a bundle** (native, the usual
  case): `Session::for_stack`, so no navigation at all. The cache key's
  navigation tag is `""` (`elab/src/cache/mod.rs:290-296`).
- **Fresh code-action session with a bundle:** `session_for`, so
  navigation with expression types, tag `"+nav+ty"`.
- **Kept session:** `load_libraries_for_probes` calls
  `enable_navigation` (`driver/src/at.rs:760`). That replaces the recorder
  (`elab/src/nav.rs:418-420`), so expression types are off and the tag is
  `"+nav"`.

The probes were already `"+nav"`, in fresh sessions as well, since they
call `enable_navigation` before loading. So code actions now read and
write the probes' cache entries instead of their own. Navigation doesn't
change what is elaborated, so the answers are the same up to time.

Code actions have wall-clock limits (`search_at.rs` `deadline`,
`per_check`, and the in-file confirmation's `options.time`). A search near
its limit can return different results in fresh and kept sessions, and
across runs, whichever key is used. Also, with a bundle, the kept
session's library is replayed under `"+nav"`, which the bundle (built
`"+nav+ty"` by `library_bundle`) doesn't hold. That only arises natively
in tests, since the browser doesn't keep sessions.

**Fix:** none needed for the answers. Say in `with_project_session`'s doc
that code actions run with navigation on and expression types off. Since
`clear_check_cache` followed by setting the bundle is only reached natively
when a bundle is set, a test should cover it (see the test below).

### 8. The kept session is dropped during thread-local teardown (cosmetic)

`WARM` (`lib.rs:2956-2958`) is first touched before the first session is
built, so it is registered before `core`'s thread-locals `LEAF`/`FREEING`
(`core/src/term.rs:260-265`) and `EMPTY`/`PENDING`
(`core/src/value.rs:400-405`). Those are first touched while a term or
value is freed during the library load.

Where thread-local destructors run in reverse order of registration
(the usual order on macOS and glibc), `LEAF` is gone by the time `WARM`'s
destructor drops the session. `Term::drop` then returns early ("the thread
is ending", `term.rs:233-235`), and Rust frees the term's children
*recursively*. The same happens in `Values::drop`.

At 64 MB of stack (`cli/src/main.rs:509`) this probably survives the
library's deepest terms. But it is the stack overflow the iterative freeing
exists to prevent, now on every server shutdown, and on every test thread
that ran a project search.

**Fix:** at the end of `search_worker`, after the job loop, drop the
session explicitly with `WARM.with(|w| w.borrow_mut().take());`, while every
thread-local is still alive. `Searcher` (used on test threads) could expose
a `release()` the tests call, or the same `take` could go in a `Drop` for
the searcher's thread.

**Test:** none cheap. A test thread that runs one project search and
then exits, under `ulimit -s`-style small stacks, would show it. The fix
is one line.

### 9. Small points in the change itself (cosmetic)

- `lib.rs:2989-2994`: if the library doesn't load, the fallback calls
  `f` on that session. `f` loads the library again through
  `probe_project` → `load_libraries_for_probes`, or `search_at_project`,
  so a failing library is loaded twice per request. The answer is the
  same (None, or "the library didn't load"), but it costs twice the time.
  Return the failure directly, or skip the load in `f` (a `loaded_failed`
  flag).
- `lib.rs:2988`: the first project's check cache loads the library for
  every later project. That is right if the cache is correct. It does mean
  project B's `.stitchwort/cache` no longer gets library entries from
  searches; the checker thread writes them anyway.
- `lib.rs:3009`: the rewind runs before the answer is sent, so it is on
  the request's latency. At the measured 1 ms total this doesn't matter.
  Rewinding at the start of the next request instead would take it off
  the critical path, but would keep the last request's state in memory
  between requests.
- `crates/lsp/tests/it/features.rs:955-972`: the `run` closure is built
  and then discarded (`let _ = run;`). Remove it.

## What I checked and found fine

- **What a request sets that a rewind doesn't restore** (elaborator
  `Options`, `elab/src/rewind.rs:120-150`: "settings stay"):
  - The check cache is cleared and set again at the start of every
    request (`lib.rs:3001-3006`), then replaced by `probe_project`
    (`at.rs:775-777`) or `search_at_project`'s `Gated` store
    (`search_at.rs:1685-1690`) whenever the project has a cache. So the
    store each request uses matches a fresh session's.
  - `Gated.writable` being left `false` on an early return doesn't
    matter: the store is replaced.
  - No other option is written on these paths: `limits` is set once in
    `for_stack`, and nothing else is assigned in `at.rs`, `search_at.rs`
    or `project.rs`.
- **Include files and the next include location:** both are in the
  session state and put back by the rewind (`state/session.rs:175`;
  `state/unit.rs`). Neither is in `Options`.
- **The probe slots** (`goals.probe`): every probe request overwrites the
  whole `Probe` (`goals.rs:638-660`), and the rewind resets `goals`
  (`rewind.rs:145`). So a probe that was never reached (a position in a
  signature) can't fire in the next request, even though file ids repeat
  after a rewind.
- **File ids and syntax addresses:** `SourceMap` ids are its length
  (`syntax/src/source.rs:92`) and are truncated back. The dot-call caches,
  keyed by syntax address, are emptied at every rewind and before every
  declaration (SW-1800, `state/caches.rs:117-139`). The other caches are
  cut by `DefId`.
- **Kernel state:** definitions, data types and builtins are cut
  (`core/src/globals.rs:715-728`), the content-hash caches are cut
  (`forget_from`), and the budget is reset. That clears steps, limits,
  `cancelled` and `exhausted`. The deadline is set and cleared around
  every check in `search_at.rs:562-576`, and `timed_out` is taken there
  too. `ran_out_in`, `deepest` and `too_large` survive, but each is
  written whenever it is read.
- **Counters that survive** (`state/session.rs:161-170`): `source_epoch`
  only ever increases, by design. `standalone_inputs` is REPL-only.
  `cache_stats`, `stats` and `instance_waits` are statistics. The library
  interface digest is a function of the library index, which is constant.
  None of these reaches a printed name. There's no global name interner.
  Meta ids live in the inference state, which a rewind empties.
- **Project changes between requests:** every request reads the
  project's configuration, source list and texts again through `Overlay`
  (`at.rs:780-786`, `search_at.rs:1700`). The project's namespaces, names,
  sources, keys, paths and library reach are all put back to the mark,
  where they are empty (`state/session.rs:149-182`). Nothing
  project-specific survives, so edits to the file, to other files or to
  `stitchwort.toml`, or a switch to another project, need no
  invalidation.
- **Library changes:** std is read once per process, so the whole server
  already never sees a std edit. If std ever becomes reloadable, the key
  must change (finding 5).
- **Nested marks:** `load_namespaces_for` (`driver/src/project.rs:437`)
  takes a mark that is never released. The outer rewind to the warm mark
  drops it ("checkpoints opened after it are dropped",
  `state/journal.rs:504-511`), so the journal's open checkpoints stay at
  one between requests. No transaction can be left open: each one is
  begun and ended inside `elaborate_namespace_cached`.
- **Navigation recorder:** it is turned on before the mark, and its maps
  and lists are put back by the journal and `NavMark`
  (`state/presentation.rs:57-69`). `enable_navigation` isn't called after
  the mark: `load_libraries_for_probes` returns early once the library is
  loaded (`at.rs:757`). Without that early return, the call would replace
  the recorder under an open mark.
- **Split patterns:** `then(session, found)` runs inside the closure,
  before the rewind (`lib.rs:2900-2910`). So `constructor_patterns` sees
  the project's types.
- **Threads:** the session is per thread, with a default of one search
  worker (`lib.rs:127`), so 0.45 GB a worker. With `search_workers = 2`
  (only the CLI's server test sets it) the cost doubles. There's no
  sharing between threads, so no races.
- **Panics:** the session is taken out of the thread-local before use, so
  an unwinding panic drops it rather than leaving it half-used for the
  next request. The thread itself dies (finding 3). A panic inside
  `rewind` drops it too.
- **Lazy-loading equations of library definitions after the mark**
  (`generate_deferred_equations`): the definitions are cut by length, and
  `equations_done` is a `GrowVec`, also cut.
- **The browser:** off (`cfg(not(target_family = "wasm"))`), as stated.

## The test

`searches_in_a_row_give_what_fresh_ones_do`
(`crates/lsp/tests/it/features.rs:991`) covers eight searches from one
project of one file: three completions on different texts, three
contexts and two code actions. It runs them once per thread and all on
one thread, and compares the results. It does exercise the kept path:
`/memory/proj` is a project, and the memory source has a check cache.

What it wouldn't catch:

- **Leaks** (findings 1, 2): it compares answers, not the state left
  behind.
- **The same request repeated** (A, B, A), the cheapest way to see drift.
- **Several namespaces or projects:** one file, one namespace, so nothing
  checks that another namespace's or project's state is gone after the
  rewind.
- **Failed and unreached requests:** a probe in a signature, a code
  action off any goal, a project that doesn't analyse. These return early
  and are where a missing reset would show.
- **The bundle and no-cache branches** of `with_project_session`
  (`lib.rs:3001-3006`).
- **Timing:** the code-action comparison depends on wall-clock limits
  (finding 7), which could make it flaky on a loaded machine.

Sharper tests, in order of value:

1. **A driver-level differential sequence**, new, for example in
   `crates/driver/tests/projects/kept_session.rs`. No LSP is needed. Build
   the kept session as `with_project_session` does (`for_stack`,
   `use_test_std_cache`, `load_libraries_for_probes`, `mark`). Use a small
   multi-namespace project in memory (three namespaces, one failing
   theorem, a number match with a `_` arm, a data type to split).

   From a fixed seed, draw about 60 steps. Each step is one of:
   - a probe: `context_at_project`, `members_at_project` or
     `split_patterns`, at a random position;
   - an edit: replace a random token of a random file, or add or remove
     a namespace in the configuration;
   - a repeat of an earlier step.

   Run each probe on the kept session (then rewind) and on a fresh
   session, and assert the answers are equal. Every tenth step, also
   assert:
   - the kept session's canonical dump at the mark equals the one taken
     just after the mark (the `outcome` of `rewind.rs:100`);
   - `journal_stats().open == 1`;
   - the lengths of `counterexample_log` and `apart_sets` haven't grown.

   Leave code actions out of this test, or give them a step budget instead
   of time, so it can't be flaky. With the test std cache, a probe costs
   milliseconds warm and about half a second fresh, so 60 steps is about
   30 s. That is too slow for the lane tier; see D2583.
2. **A cheap version of 1 for the lane tier:** the same project, a fixed
   list of 10 steps including one failed probe, one edit of another
   namespace and one repeat. Under 10 s.
3. **The `with_project_session` branches:** run the existing test once
   more with `Options::library` set (the bundle branch), and once with a
   `Memory` without a cache.
4. **Panic recovery** (with finding 3's fix): a search that panics,
   followed by one that must answer. It needs a test seam (D2584).

The exact commands I'd run, none of which were run here:

```
nix develop -c task test:one -- searches_in_a_row_give_what_fresh_ones_do
nix develop -c task test:one -- kept_session      # the new test 1/2, once written
```

## Questions for Matt

- **D2583:** Should the long randomised check of the kept session (about
  60 steps, about 30 s) run in the daily tier, with a 10-step version in
  the lane tier? [rec: yes. The kept session lives for hours in the
  editor, and only a long sequence shows drift or growth.]
- **D2584:** Should a panic in a proof search be caught, answered as "no
  result" and logged, so the editor keeps its searches? Today the search
  thread dies and searches stop until the editor restarts. [rec: yes. It
  is a small change; a test-only way to make a search panic would come
  with it.]

Findings worth filing as tickets (small, Sonnet):

- 1, the counterexample logs: turn the searches off in probes, or cut
  the log at a rewind.
- 2, intern `apart_sets` (Opus, being kernel state).
- 3 together with 6: catch panics in `run_search`, and either wire in
  cancellation or correct the comment.
- 4 and 8: one-line hardening fixes (4 goes to Opus).
- 9: the clean-ups.
