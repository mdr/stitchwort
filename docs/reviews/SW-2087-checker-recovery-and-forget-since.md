# Review of SW-1948 and SW-1925 (SW-2087)

A fresh-eyes review, from the code only, of two merges of 7 Nov 2026:

- `b0fd0473c`, **SW-1948**: the language server's checker recovers from a
  panic on a fresh thread (`crates/lsp/src/lib.rs`, about 550 lines, by
  Sonnet). The design is stage 3 of `docs/proposals/lsp-failure-policy.md`,
  with D2740 to D2742.
- `28e0b7855`, **SW-1925**: a refused check-cache replay is undone through
  `Kernel::forget_since` (`crates/core/src/globals.rs`), and
  `Builtins::mark`/`rewind`/`dump` name every field
  (`crates/core/src/native.rs`). The design is
  `docs/proposals/check-cache-trust.md`.

Nothing was built or run. Line numbers are those on `main` at `c6e620142`.

## Summary

**SW-1925 is sound.** I found nothing that `forget_since` misses in the
kernel. That covers the registry, every field of `Builtins`, the hashes and
erasure caches, and the pins, which hold no state. Leaving the budget alone
is right at both of its callers. What I found is small: a refusal count that
includes cancellations, a witness that covers less than its doc says, a
witness cost paid on every replay in every dev and test build, and two
missing tests. The one real budget bug in this area, `rewind_globals`, is
already SW-1995, which is in progress.

**SW-1948 does what it says in the common case.** I found no deadlock, no
version-ordering bug and no thread-local that survives a restart. Two
things undermine its purpose, though, which is to contain a bug that one
project's text triggers:

- a panic while the successor reopens documents is uncaught (the lane said
  so). A project that panics while it loads therefore stops checking
  everywhere, with stale diagnostics left on screen;
- the restart budget is session-wide, and each edit to a broken project
  costs two restarts. So one open and two edits to a single broken project
  switch checking off for every project. That is the frozen editor SW-1948
  was filed for, reached in seconds.

Top five recommendations:

1. **Reopen under the catch** (C1, high). Replay the open documents inside
   `run_caught`, as ordinary `Open` edits, so that a panic there is
   attributed to its workspace and quarantines it on the second try. Hand
   the `Keeper` back before the sessions are dropped.
2. **Stop one broken project from spending everyone's budget** (C2, high;
   D2980). Give each project a budget of its own, and let its first panic
   after a retry quarantine it again.
3. **Don't let the light bulb spend the search budget** (C3, medium).
   Remember a search that panicked, by document version and goal, and
   answer null without running it again until the text changes.
4. **Record diagnostics as published only once they are sent** (C4, low).
   Then a panic in `publish` can't leave the successor suppressing
   diagnostics the client never got.
5. **Close the SW-1925 loose ends in one small lane** (K2 to K6, low).
   Don't count a cancellation as a refusal. Cover the hash caches in the
   witness, and make the witness cheap. Fix `Kernel::rewind`'s doc, and add
   the two missing tests.

Findings: 2 high, 2 medium (one of them already filed as SW-1995), 13 low.

## Findings

| # | Where | What | Severity | Confidence | Size |
|---|---|---|---|---|---|
| C1 | `lsp/src/lib.rs:2416`, `:2421`, `:2545` | A panic while the successor reopens documents is uncaught: checking stops everywhere, the `Keeper` is lost, and stale diagnostics stay on screen | high | high | M |
| C2 | `lib.rs:2407`, `:2454`, `:2975` | The session-wide budget lets one broken project stop checking of every project after one open and two edits; each retry costs two restarts and rebuilds every workspace | high | high | S + D2980 |
| C3 | `lib.rs:685-721` | The editor's automatic code-action requests at a goal whose search panics spend the search budget in seconds | medium | medium | S |
| K1 | `elab/src/lib.rs:1122` | `rewind_globals` still calls `Kernel::rewind` mid-declaration, which the new docs on `rewind` and `mark` contradict (**SW-1995**, in progress) | medium | high | (filed) |
| C4 | `lib.rs:2887`, `:2897` | `publish` records diagnostics as published before sending them; a panic in between makes the successor suppress them | low | high | S |
| C5 | `lib.rs:2584`, `:2597`, `:2970` | Workspace keys disagree for a file on its own inside a project folder: an edit never lifts its quarantine, and its `Close` leaves its session behind | low | medium | S |
| C6 | `lib.rs:685`, `:714` | One budget per search worker, not one shared; a stopped supervisor keeps taking jobs from the shared queue and answers its share with null | low | high | S |
| C7 | `lib.rs:2446` | The stop message names a "Stitchwort: Restart Server" command that doesn't exist yet (SW-1980 is in backlog) | low | high | S |
| C8 | `lib.rs:2438`, `:2474`; `:2999` | Smaller: a recovered checker panic is logged twice; in stopped mode a `Close` leaves the error diagnostic in Problems | low | high | S |
| C9 | `lsp/tests/it/faults.rs` | Test gaps: no panic in `apply`, no double fault, no file on its own (the proposal's test 2), no `Close` of a quarantined file; rebuild time not measured | low | high | M |
| K2 | `elab/src/cache/mod.rs:2637`, `:2685` | A cancelled (or out-of-budget) kernel call during replay counts as a refusal, which is documented "never expected" | low | medium | S |
| K3 | `cache/mod.rs:2627`, `globals.rs:764` | The undo witness doesn't cover `EvalCaches` (hashes by id, erasure), which pin checks and cache keys read | low | high | S |
| K4 | `cache/mod.rs:2627` | The witness formats the whole registry and `Builtins` for every replayed entry in every dev, test and bench build, to throw away on success | low | medium | S |
| K5 | `globals.rs:752` | `Kernel::rewind`'s doc says the cancellation flag is cleared; `Budget::reset` keeps the flag and clears only the noted state | low | high | S |
| K6 | `driver/tests/projects/check_cache.rs` | Test gaps: no test of the early refusal of a namespace entry that binds built-ins; nothing fails if `forget_since` is swapped for `rewind` | low | high | S |
| N1 | `faults.rs:203`, `check_cache.rs:1067` | Two test docs narrate the old behaviour | low | high | S |

## Details: SW-1948

### C1. The double fault: a panic while reopening (high)

`keep_checker` spawns each checker thread with
`Checker::resume(...).run(&edits)` (`lib.rs:2416`). `resume` calls
`reopen` (`:2545`), and so `open_text`, `set_text`, `open_workspace`,
`load_project` and `LiveProject::new_except`, *before* `run`'s catches. That
is not cheap code: `new_except` loads the libraries
(`driver/src/live.rs:475`), which replays the check cache and runs the
kernel. It also holds `admit_replayed`'s new undo assertion in dev builds.
`give_also` runs there as well.

**Scenario.** A project whose loading panics every time, say a library
replay bug:

1. The `Open` panics in `apply`. It is caught and attributed to the project
   (a suspect), and a successor is started.
2. The successor's `resume` panics on the same document. The join gives
   `Err`, and the `Ok(Err(_)) | Err(_)` branch (`:2421`) sends "stopped
   checking after an internal error" and returns.
3. The `Keeper` was moved into the dead thread, so nothing publishes a
   diagnostic per file. Every project's last diagnostics stay on screen as
   if current, which D2543 and proposal §3.1 item 6 rule out ("never a stale
   answer passed off as current").
4. A server restart doesn't help: the file is still open, so it happens
   again.

The quarantine was designed for exactly this case, and it never applies.
The lane reported the gap. I rate it high because it brings back SW-1948's
own symptom, for the class of bug most likely to hit at load.

**Change (M).**
- Make `resume` only restore the fields.
- Start `run_caught` by replaying each recorded document as
  `apply_caught(Edit::Open { .. })`, then the focus, each under the
  existing catch. A panic there becomes an ordinary `Exit::Panicked` with
  its workspace, and the second one quarantines it. Re-recording the text
  is harmless.
- In `run`, take `work` out of `self` and build the `Keeper` before dropping
  the sessions, then send the `Keeper` back. Then a panic in a session's
  `Drop` loses nothing either.
- Test: a fault hook in `open_workspace` for one project. Expect that
  project's quarantine diagnostic and the other project's own diagnostics.

### C2. One broken project spends the whole session's budget (high; D2980)

D2741 quarantines a project that "panics again before any edit to it", and
an edit lifts the quarantine. `edited` (`:2970-2976`) also clears the
project from `suspects`. So after an edit, the retry's first panic only
makes it a suspect again (`:2454`, a restart). The second panic quarantines
it (another restart).

Each edit to a project that panics every time therefore costs **two** of the
session's 5 restarts. `edited` runs for `Open` too, so opening another file
of a quarantined project also counts as an edit. The budget test confirms
the arithmetic (`faults.rs`, "Two panics for each edit ... the sixth is one
too many"): one open and two edits, and checking stops **for every
project**.

Someone typing in a file that triggers an elaborator bug sends an edit at
every pause. They reach the stop in seconds, and after a restart they reach
it again in two more pauses. Each restart also rebuilds every open
workspace, so the other projects re-replay their libraries twice per pause
until then.

The design's own words were "one retry per edit, inside the budget"
(§3.1 item 5). The aim was to contain a repeating bug to one project. With a
session-wide budget, any project that keeps being edited defeats that aim.

**Change.**
- The retry rule (S, mine to decide as implementation): keep the workspace
  in `suspects` when an edit lifts its quarantine. Then a retry's first
  panic quarantines it again, at one restart per edit.
- The budget's scope is Matt's (D2980). My recommendation is a budget per
  project (the same 5 in 3 minutes). Past it, the project stays quarantined
  until a restart, and the pop-up says so. The session budget then counts
  only panics that no project is blamed for.

### C3. The light bulb spends the search budget (medium)

VS Code asks for code actions whenever the cursor moves or the diagnostics
change. At an open goal, `code_action` queues a search. If that goal's search
panics every time, five such requests in 3 minutes switch proof searches off
for the session (`:707-720`). The budget test does it with seven
`code_action` calls. Each restart also reloads the library on the next
project search.

**Change (S).** Keep a small set of the searches that panicked:
`(uri, version, kind, goal range)`. Answer a repeat with null at once,
without running it or spending the budget. A new version of the text clears
its entries. A goal that panics then costs one restart per edit, not one
per cursor move.

### C4. Published before it is sent (low)

`publish` (`:2845`) inserts each file's `(version, diagnostics)` into
`self.published` inside the loop (`:2887`). It sends the notifications only
after the loop, once the nav guard is dropped (`:2897`).

If `diagnostic`, `goals_kept` or `ws.store` panics on a later file, the
earlier files are in `published` but were never sent. The `Keeper` carries
`published` to the successor. The successor computes the same diagnostics
and suppresses them as unchanged (`published.get(&uri) == Some(&shown)`), so
the client keeps an older version's diagnostics until the next real change.
`goals_kept` also reads that entry as "what the client has".

That needs a panic inside `publish`, which is unlikely. The mechanism is
certain, though, and it defeats the design's reliance on `published`
(§3.1 item 4).

**Change (S):** insert into `published` in the send loop, after each send.

### C5. Two ideas of a file's workspace (low)

A file inside a project folder can be checked on its own: it is outside the
project's `sources`, or the folder's `stitchwort.yaml` can't be read. Its
work key is then the file's path (`open_workspace`). A step panic
quarantines that path. While the file is quarantined its session isn't
loaded, so `workspace_of` (`:2597`) falls through to `find_project` and
returns the **folder**. As a result:

- `edited` never lifts the file's quarantine, nor clears its suspicion. The
  edit still checks it, because `apply`'s `set_text` path doesn't consult
  the quarantine.
- The next panic after an edit quarantines it at once.
- Its `Close` takes the quarantine branch (`:3008`), which leaves the new
  `Work::File` in `work`.
- An edit to the loose file lifts the *project's* quarantine, if the project
  has one.

**Change (S):** decide a path's key in one place. For example, record the
key each open path was opened under, and carry it in the `Keeper`. Use that
in `step` attribution, `quarantine_key`, `workspace_of` and `edited`.

### C6. Per-worker search budgets (low)

The merge message and the ticket say the search workers share the budget.
In fact each `keep_search_worker` has its own (`:685`). A supervisor whose
budget is spent drains the *shared* job channel (`:714`). Every job it
happens to take is answered with null, while the other workers go on
searching, under a pop-up that says searches have stopped. This only shows
with more than one worker, which only tests configure (`search_workers: 1`
by default).

**Change (S):** one `Arc<Mutex<Budget>>` and one "searches off" flag for the
pool. When the flag is set, every worker answers null.

### C7 and C8. Small things (low)

- C7: the checker's stop message (`:2446`) tells the user to run
  "Stitchwort: Restart Server". No such command exists yet (SW-1980,
  backlog). Do SW-1980 first, or say "reload the window" until then.
- C8: a recovered checker panic is logged twice: `keep_checker`'s
  `eprintln!` (`:2438`), then `Notices::recovered`'s (`:2474`). In stopped
  mode, `Close` (`:2999`) removes the version but doesn't clear the file's
  error diagnostic, unlike the quarantine branch. So the error stays in
  Problems for a closed file.

### C9. Test gaps (low)

- Every checker test injects its fault in `step`. Nothing covers a panic in
  `apply` and its attribution through `workspace_of`, or C1's double fault.
- The proposal's test 2 asked for "a file on its own that doesn't" panic.
  The test uses a second project instead, which is why C5 went unseen.
- Nothing covers a `Close` of a quarantined file, which should publish
  empty diagnostics.
- The ticket asked to "measure the time to rebuild one AoC project". The
  report doesn't give it. Each restart rebuilds every open workspace, so
  that number decides how much C2 costs.

## Details: SW-1925

### K1. `rewind_globals` (medium, filed)

`rewind_globals` (`elab/src/lib.rs:1122`) still calls `Kernel::rewind`. That
resets the running operation's step limit, stack floor and noted
cancellation, partway through a declaration. The merge's new doc on
`Kernel::rewind` says it is for when no operation is running. Its new doc
on `Kernel::mark` names `rewind_globals` as a mid-declaration caller. That
is proposal §8 ticket 3, now **SW-1995**, in progress. Nothing new to file;
that lane should leave the two docs agreeing.

### K2. A cancellation counts as a refusal (low)

`submit` maps every kernel `Diagnostic` to `Bad("refused: …")` (`:2685`).
So when a kernel call is cancelled or runs out of its limits during a
replay, `admit_replayed` counts `Stats::refused` (`:2637`), undoes, and the
file is elaborated (and cancelled in turn). In the editor every keystroke
can cancel a replay, so `refused` (documented "never expected", and so a
signal of a missing key input) becomes noise there. The differential tests
don't cancel, so they don't see it. Nothing wrong is written: a cancelled
check isn't written (`:408`).

**Change (S):** in the `Err` branch, still undo, but if
`machine.budget.cancelled()` or the budget is exhausted, don't count the
refusal and don't elaborate as for a miss.

### K3. The witness covers less than it says (low)

The test docs say the undo is "checked ... against the kernel at the mark".
`bindings_dump` covers the counts, the registry and `Builtins`, and with a
forced refusal the declarations too. It doesn't cover `EvalCaches`: the
content hashes by `DefId`/`DataId`, and `erasure_defs`.

Those matter. Pin checks (`pins::check_def` → `def_hash`) and cache keys
read the hashes. A hash left behind for a removed id would be read once
elaboration reuses the id. A pin could then pass for the wrong body, and
the pins exist for soundness. `forget_from` handles this correctly today,
so this is a guard against regressions, not a bug.

**Change (S):** add to the witness the number of hash keys at or past the
mark (always 0 after the undo) and `erasure_defs.len()`. Don't compare the
whole map: a replay legitimately adds hashes for older ids.

### K4. The witness's cost (low, unmeasured)

`CHECK_UNDOS` is on in every build with `reference`. That is every dev and
test build, and the bench crate too (it depends on `stitchwort-dev-features`).
So every replayed entry (each library file and each namespace) formats about
two to three hundred lines (`Builtin::ALL`, natives, primitives, float defs)
before `submit`, and throws them away on success, the normal case. I'd
guess tens of µs per entry and a few ms per session that loads the library
from the cache. Across a test run that makes thousands of sessions, that
adds seconds, and it shows up in the dev-loop timings now being tuned.

**Change (S):** measure first. If it shows, compare a cheap fingerprint
every time: the counts, the map lengths, the scalar fields and the number of
registry entries. That is enough, because every binding is keyed by a new
id and `unbound` refuses rebinding. Keep the full text for forced
refusals, where it gives the message.

### K5. `Kernel::rewind`'s doc (low)

`globals.rs:752` says "The cancellation flag is cleared with the rest of the
budget". `Budget::reset` keeps the shared flag ("the flag's owner clears
it") and clears only the noted `cancelled` state. Say "the noted
cancellation".

### K6. Test gaps (low)

- Proposal §8 ticket 1 asked for "the namespace case". The new namespace
  test covers a refusal partway through. Nothing covers the new early
  refusal of a namespace entry with a non-empty `bound` (`:2616-2618`).
- Nothing fails if `admit_replayed` calls `Kernel::rewind` instead of
  `forget_since`: the results are the same. A core unit test would pin it:
  start an operation with a step limit, mark, declare, `forget_since`, and
  assert the limit and the stack floor are unchanged (and that `rewind`
  does reset them).

### N1. Comments that narrate (low)

- `faults.rs:203`: "a panic in the checker used to end its thread
  silently".
- `check_cache.rs:1067`: "With the undo that removed only declarations,
  this fails on `float`".

Both describe the old version. The test name and the assertion say what is
checked; the history belongs in the commit message.

## Checked and sound

SW-1948:
- **No thread-local survives a restart.** Every successor is a fresh
  thread. The sessions are dropped on the dying thread after the unwind has
  finished. `NO_ETA` (`unify.rs:1672`, still without a guard) and the
  core's memos die with the thread.
- **The main thread can't carry `NO_ETA` either.** Its request catch
  (`Main::request`) runs no elaboration: code actions, the context and
  member completion go to search threads.
- **The `Keeper` really is plain data.** It is moved into `spawn`, so the
  compiler requires it to be `Send`. No `Rc` can cross.
- **Version order holds.** `record` runs first in `apply`. The edit
  channel is FIFO and shared, so edits that arrive during a restart are
  applied after the reopen, in order. The edit that panicked is reopened
  from its recorded text.
- **No deadlock.** The supervisor holds no lock while it joins. The edits
  channel is unbounded. Nav and journal locks recover from poisoning
  (`into_inner`). At shutdown a successor sees the channel closed and ends.
  A spent search supervisor drains until `Main` drops the sender.
- **Carried state is consistent.** `requests` is carried over, so refresh
  ids stay unique. `announced` and the quarantine and stopped paths still
  send `stitchwort/checked` for the right versions, because the quarantined
  workspaces have no pending work. The stopped mode forgets nav and puts an
  error on every open file. `Notices` keeps the first-only pop-up (D2742).
- **Process-wide state holds nothing that matters.** The nav parse caches
  (`driver/src/nav.rs:164`) lock only around map operations. The timing
  tables exist only with `STITCHWORT_TIMINGS`.

SW-1925:
- **The undo covers all of the kernel's declaration state.** `Kernel`,
  `Builtins::mark`, `Builtins::rewind` and `Builtins::dump` destructure every
  field. The registry can't be rebound (`unbound` filters bound built-ins),
  so `forget_from` restores it exactly. Natives, primitives and float defs
  are keyed by new ids only. `Text`/`Float`/`nat_add_rule` are restored
  from the mark.
- **The pins hold no state.** `pins.rs` keeps none. Its hashes go through
  `EvalCaches`, which `forget_from` cuts.
- **The tree memos don't survive.** `TREE_MEMO` and `EQUAL_CALLS` empty at
  the end of the outermost comparison. Replay runs between kernel calls,
  not inside one.
- **The budget is right at both callers.** `kernel_op` scopes each kernel
  call's budget (`start`/`restore`), so a refused replay leaves the
  enclosing operation as it was, for library entries and namespace entries
  alike.
- **Binding only for library entries matches elaboration.** All four
  elaboration call sites bind only while `loading_prelude`.
- **The elaborator's side is consistent.** Between the mark and the undo,
  only kernel calls and built-in registration run. So truncating `owners`
  and `paths` is all the elaborator needs. That invariant lives only in the
  code's shape; elab `Caches` would need `rewind` if elaboration ever ran
  there.

## The 1 Nov review's findings in scope

- **§1.4** (unbounded search threads, unversioned code-action edits):
  fixed before these merges. The pool is bounded (`search_workers`), and
  edits are versioned when the client supports `documentChanges`.
- **§1.5** (`Globals` exposes mutable declaration vectors): fixed. `Env`'s
  fields are private, writes go through `pub(crate)` accessors, and the
  bypasses are behind `test-bypass`.
- **§4.1** (save/restore pairs without guards; "panicked sessions are
  discarded"): the policy is now implemented for the checker and the search
  workers. The session and the thread are discarded. Still open: the
  `NO_ETA` guard and the per-candidate catch at `search.rs:1402` (proposal
  stage 2, D2743).
- **§6.5** ("group state ... the maintenance list shared by rollback,
  rewind, cache replay and canonical dumps"): improved. There is one undo
  primitive, `Builtins` is destructured everywhere, and the canonical dump
  and the witness share `Registry::dump` and `Builtins::dump`. The
  elaborator's side of a replay undo is still a separate hand-kept list
  (above).

## Tickets to file

1. **[Sonnet] Checker recovery: reopen under the catch, one workspace key,
   publish after send** (75 min; Opus if it stalls). C1, C4, C5, C2's retry
   rule, C8, and C9's tests:
   - a fault hook in `open_workspace` (the double fault, quarantined);
   - a panic in `apply`;
   - a file on its own in a project folder, quarantined and then lifted by
     an edit;
   - a `Close` of a quarantined file.

   Measure the rebuild time of one AoC project after a restart. Tests:
   `task test:one -- -E 'binary(it) & test(/^faults::/)'` and the threaded
   `lsp::` diagnostics tests.
2. **[Sonnet] Search budget: shared, and not spent by the light bulb**
   (45 min). C3, C6 and C7's wording, or do SW-1980 first. Tests: the
   `faults::` search tests, plus one that repeats a code action at a
   panicking goal and expects one restart.
3. **[Sonnet] Per-project restart budget** (45 min, after D2980; can fold
   into lane 1 if D2980 is answered first). C2.
4. **[Sonnet] Replay-undo follow-ups** (45 min). These are near the trust
   boundary, so Sonnet rather than DeepSeek. K2 to K6 and N1: don't count a
   cancellation as a refusal; add `EvalCaches` to the witness; a cheap
   fingerprint, measured; the `rewind` doc; the namespace-`bound` test; the
   core budget test. Tests: `task test:one --` the new tests,
   `check_cache::a_namespace_entry_refused_part_way_gives_the_same_result`,
   `check_cache::a_refused_library_entry_takes_back_its_float_bindings`.

K1 is SW-1995 (in progress). Add to its brief: leave the docs on
`Kernel::mark` and `Kernel::rewind` agreeing with its callers.

## Questions for Matt

- **D2980:** When one project keeps panicking each time it is edited,
  should its retries count against a budget of its own (5 in 3 minutes,
  after which that project stays quarantined until a restart), rather than
  the session-wide budget, which today stops checking for every project
  after one open and two edits? [rec: yes. Today one broken file can switch
  off checking everywhere in a few typing pauses, which is the frozen
  editor SW-1948 set out to fix. A per-project budget still fails visibly
  (D2543) and keeps the other projects working. Decided here as
  implementation: a retry's first panic quarantines the project again, so
  each edit costs one restart, not two.]
