# Review of SW-2088, SW-2089 and SW-2091: language server recovery, round 3 (SW-2116)

Reviewed by reading only, on 7 Nov 2026, at `c875efca6`. The merges are
`a7b060b37` (SW-2088), `1a6f03192` (SW-2089) and `827b00003` (SW-2091), read
with `git diff <merge>^1 <merge>`, together with the code around them in
`crates/lsp/src/lib.rs` and `crates/lsp/src/source.rs`. Nothing was built or
run. Background: `docs/proposals/lsp-failure-policy.md`,
`docs/reviews/SW-2087-checker-recovery-and-forget-since.md` and
`docs/reviews/SW-2094-unifier-gaps-and-recovery.md`.

## Summary

Most of the earlier findings are really fixed. The search side is in good
shape: a panicking goal now costs one restart per version, not one per
cursor move, and nothing on that side can restart in a loop. The checker's
per-project budget, the retired set and D3000 work as the tests say. The
`Keeper` is built before the sessions drop. But the checker still has one
weak point, and SW-2091 made it worse: the key a file is kept under is
**worked out again at every lookup**, from the disk, and it doesn't always
come out the same. Two cases produce a different key: L2's fix (SW-2091's
`Source::sources`), and L1's fallback key (the file's own path, when working
out the project panics). The quarantine and the retired set are then looked
up under a key they were never stored under. The project is never held. With
no user action, the successor checks it again, panics again, and loops
through the session's 15 restarts in a burst of error pop-ups. Then checking
stops for every project, the outcome the policy exists to prevent. The fix
is the one SW-2087 C5 first proposed: decide each open path's key once,
record it, and carry it in the `Keeper`.

**Top five recommendations**

1. Record the key each open path was opened under, and carry it in the
   `Keeper`. Look it up before working anything out (R1, R2).
2. Have `home_of` catch its own panic and give the fallback, so every
   caller gets the same key, not just `blame` (R2).
3. Don't let a successor replay an unattributed panic. On an unattributed
   panic, drop `also` before the next restart (R3).
4. Add the missing fault tests: a persistent config-read panic, a project
   whose config parses but whose files don't load, a panic in reopening
   with no project to blame, and the backstop actually reached (R11).
5. Show one pop-up per quarantine, not one per retried edit. Make the
   remedy text agree ("Reload the window") (R5, R9).

Findings: 1 high, 1 medium, 10 low.

## Findings

| # | Where | What | Severity | Confidence | Size |
|---|---|---|---|---|---|
| R1 | `lib.rs:2732-2745` (`home_of`), `:3318-3326` (`open_workspace`), `source.rs:109-120` | `home_of` now decides from the config alone. `open_workspace` still keys the file on its own when `Source::project` fails (a listed source folder is missing, or a walk error). A step panic is quarantined under the file's path, but every later lookup finds the folder, so the successor checks the file again and loops to the backstop: checking stops everywhere, with no user action. SW-2087 C5 is back | high | high (mechanism), medium (how often) | M (with R2) |
| R2 | `lib.rs:2814-2817` (`blame`), `:2709-2716`, `:3134-3140` | L1's fix covers only a fault that happens once. A config read that always panics is blamed on the file's path. But `quarantine_key`, `edited`'s retired check and `open_workspace` each call `home_of` again, outside `blame`'s catch, and panic again. So quarantine and retirement can't hold: the restarts loop to the backstop, with about 8 error pop-ups. It also blames the wrong project: `edited`'s loop over the other open files blames a panic in *their* project on the edited one | medium | high | S (in R1's lane) |
| R3 | `lib.rs:2693`, `:3244-3247` | A panic in `give_also` (a `Focus` edit, no path) is blamed on nobody. `also` already holds the new paths, so the `Keeper` carries them, and the successor's `reopen` runs `give_also` again and panics again. The restarts loop to the backstop. The same goes for any panic in reopening that repeats and can't be blamed on a workspace | low | high (mechanism), low (how often) | S |
| R4 | `lib.rs:2484-2488`, `:2541-2545` | Every panic spends the backstop, including the one that retires a project. So a project costs 6 of the 15 restarts, not 5, and the third broken project being edited stops checking everywhere before it can be retired. The doc's "three projects' worth" doesn't hold | low | high | S |
| R5 | `lib.rs:2556-2568` | Each retry that panics again sends a fresh ERROR pop-up ("stopped checking proj"). Editing a broken project raises one toast per pause in typing, until it is retired (the test counts 5) | low | high | S |
| R6 | `lib.rs:580-582`, `:1316-1320`, `:1344` | The panicked-search key is (document, version, what was asked). The answer also depends on the other open files of the project (`SearchTarget.project`), its config and the cache. Fix the other file, and this one's search is still answered null until this document changes | low | high | S |
| R7 | `lib.rs:948-950`, `:1338-1344` | A race: a worker checks the version, `document_moved` updates it and clears, then the worker inserts. The stale entry only bites if the same version number comes back, as after a close and reopen at version 1 | low | medium | S |
| R8 | `lib.rs:763-781` | C6 is only half done. The budget is shared, but a spent budget stops only the supervisor that saw it: the workers still alive go on searching under a pop-up that says searches have stopped | low | high | S |
| R9 | `lib.rs:2550-2551`, `:2572-2573` | The pop-ups say "Reload the window". The diagnostics for a stop and for a retired project still say "restart the language server", and there is no command for that yet (SW-1980 is in backlog) | low | high | S |
| R10 | `tests/it/common/mod.rs:45-55` | The new search warm-up documents a product cost. In a session whose cache has only the checker's entries, the first search checks all of std from source: "over a minute" in release, by the comment. Meanwhile the one search worker holds up every code action, `contextAt` and dot completion. The tests can no longer see it (Q5) | low | medium | measure first |
| R11 | `tests/it/faults.rs` | Test gaps: see "Missing tests" | low | high | M (with R1) |
| R12 | `source.rs:109-120` | L2's tail: `Disk::sources` logs a broken config on every call, which means every `quarantine_key` while anything is quarantined | low | high | S |

## Details

### R1. A file kept on its own is looked up as its project (high)

Before SW-2091, `home_of` asked `Source::project`. That returns `None` when
a source folder listed in the config doesn't exist, or when the walk fails
(`project_sources`, `driver/src/project.rs:1490-1508`). `home_of` then gave
the file's own path, the same key that `open_workspace` uses when
`load_project` returns `None`. SW-2091 switched `home_of` to
`Source::sources`, which only parses the config (`source.rs:109-120`). Now,
for a project whose config parses but whose files don't load:

- `open_workspace` (`:3320-3326`) gets `dir` from `home_of`, `load_project`
  fails, and the file is kept as `Work::File` under **its own path**;
- `workspace_of` on that path, once it isn't loaded, goes to `home_of`
  and returns **the folder**.

**Scenario.** A project's `stitchwort.yaml` lists `sources: [src, lib]` and
`lib/` doesn't exist yet. The user opens `src/A.sw` (checked on its own) and
hits an elaborator panic in a step. Here is what happens.

1. `step_caught` blames `src/A.sw`. It becomes a suspect, and the checker
   restarts.
2. The successor's `reopen` opens it again, and the step panics again.
   `src/A.sw` is quarantined, with a pop-up.
3. The next successor forgets it and calls `open_text`. `quarantine_key`
   computes the folder, which isn't quarantined, so `src/A.sw` is checked
   and panics. It is a suspect again (the quarantine cleared its
   suspicion).
4. Steps 2 and 3 repeat. At the sixth panic, `src/A.sw` is retired, but
   `retired` is never consulted under that key either. At the sixteenth,
   the backstop stops checking for every project.

All of that happens in one burst, one rebuild of every open workspace per
restart, with an error pop-up at every second panic. This is the regression
L2's fix brought in. The in-memory source can't show it: `Memory::project`
never fails when `Memory::sources` succeeds.

**Change (M, with R2).** Decide the key once. `open_workspace` knows the key
it actually used. Record it in a `homes: BTreeMap<PathBuf, PathBuf>`, carry
it in the `Keeper`, and have `workspace_of` consult it before working
anything out. Remove entries on `Close`. Alternatively, make `home_of` give
the path whenever `Source::project` would fail, but that reads every file
again, which L2 removed. The record is the better fix. It also ends the
whole class of bug: three reviews in a row have found a new way for keys to
disagree.

### R2. A persistent fault in finding the project (medium)

`blame` (`:2814-2817`) runs `workspace_of` under a catch and falls back to
the path. But the key is worked out again everywhere else: `quarantine_key`
(`:2709-2716`), the retired check in `edited` (`:3134-3140`), and
`open_workspace` (`:3320`). None of them has a catch. With a config read
that panics every time (L1's case: a YAML parser bug on some input), every
open, every reopen and every lookup panics.

- The open panics. It is blamed on `src/A.sw` and the checker restarts.
- Each reopen panics in `set_text` → `open_workspace` → `home_of`, or, once
  something is quarantined, in `quarantine_key`. Each panic is blamed on
  the path. The suspect/quarantine cycle runs as in R1, retiring the file
  can't stop it, and the backstop is reached with no user action.
- Each other file of that project gets a key of its own, and so a budget of
  its own.
- `edited` loops over every other open file calling `workspace_of`
  (`:3150-3156`). Editing a healthy, quarantined project P while a file of
  the broken project Q is open panics there. That panic is blamed on **P**.

The test `a_panic_while_blaming_is_caught_too` arms the fault for two
panics, so the third read succeeds and the loop never shows. With
`usize::MAX` it would end in the full stop.

**Change (S, in R1's lane).** Move the catch into `home_of` (log, then
return the path), so every caller gets the same fallback, and record that
key as in R1. Test: `sources_panic` with `usize::MAX`. Expect the file
quarantined, at most two restarts, and the other project still checked.

### R3. A successor replays an unattributed panic (low)

`apply` for `Focus` sets `self.also = paths`, then calls `give_also`
(`:3244-3247`). A panic there has no path, so it is blamed on nobody and
only spends the backstop. `take_keeper` carries the new `also`, and
`reopen_documents` ends with `self.caught(None, Checker::give_also)`
(`:2693`). So the successor panics in the same place, and so does the next
one. Fifteen restarts follow, then a full stop. The design note calls the
backstop "the only limit on panics that no workspace can be blamed for".
That is true, but it assumes such a panic doesn't repeat by itself.
**Change (S):** in `keep_checker`, when a panic has no workspace, clear
`kept.also`. More generally, a panic in reopening that has no workspace is
recorded in the `Keeper`, and the successor skips that step once.

### R4. The backstop's arithmetic (low)

`own_budget_spent` is worked out first, and then `session.spend()` runs for
the same panic (`:2541-2545`). A project is retired at its sixth panic, so
each retired project spends 6 of the session's 15. Three projects that
panic on every edit, edited within 3 minutes, stop checking everywhere at
the third project's fourth panic. The doc at `:2484-2487` says "three
projects' worth". Counting every panic is the right call: wrongly
attributed panics (R1, R2) would otherwise get a fresh budget per key. Fix
the number instead: `BACKSTOP = 3 * (RESTARTS + 1)`, or say "two". S.

### R5. A pop-up per retried edit (low)

Each time a retry panics and the project is quarantined again, the code
sends `notices.always(ERROR, "Stitchwort stopped checking {name} …")`
(`:2556-2568`). Someone typing in a file that triggers the bug gets an
error toast at each pause, five of them before retirement
(`a_projects_budget_runs_out_and_another_project_goes_on` asserts five).
The diagnostic already shows the state. **Change (S):** show the pop-up the
first time a workspace is quarantined, and again when it is retired. Keep
a `told` set in the supervisor.

### R6. The panicked-search key leaves out the other files (low)

The key (`:580`, `:934`, `:1318`) is the document, its version, and the
`SearchKind` as JSON. For a code action that's the goal's range, not the
cursor (`code_action` maps the cursor to the goal at `:1083-1091`), so C3 is
fixed. But a project search reads the other open files' text
(`search_target`, `:1269-1294`), the project's config and files on disk,
and the cache. If a goal's search in `A.sw` panics because of something in
an open `B.sw`, fixing `B.sw` leaves `A.sw`'s entry in place: no light bulb
until `A.sw` is edited. It's a harmless failure (null), cured by one
keystroke, and it never answers wrongly in any other way. **Change (S):** in
`document_moved`, clear the whole set, not just this document's entries.
VS Code only asks again for the active editor, so this costs nothing
measurable. Test: a panic at `A`, an edit to another open file, then a
search at `A` that runs.

### R7. A race between recording and forgetting (low)

The worker reads `versions` and drops the guard at the end of the `if`
condition (`:948`). Only then does it lock `panicked` and insert.
`document_moved` (`:1338-1344`) updates `versions`, then clears `panicked`.
If the clear falls between the check and the insert, an entry for the old
version survives. It only matters if that version number is asked again:
close and reopen, when a client counts from 1 again. **Change (S):** insert
while holding the `versions` guard, and clear under it.

### R8. Live workers ignore a spent budget (low)

`told_stopped` makes the pop-up appear once (`:767`). But the supervisor
that finds the budget spent is the only one that drains the queue
(`:775-783`). The other workers are alive, take jobs from the same channel
and search as usual. With `search_workers > 1`, some requests get answers
and others null, under a pop-up saying searches have stopped. **Change (S):**
a `stopped: AtomicBool` in `Searches`, set with the pop-up, which
`run_search` checks first and answers null.

### R9. Two remedies (low)

The pop-ups now say "Reload the window" (C7). The diagnostic for a full
stop (`:2550`) and for a retired project (`:2572`) still say "restart the
language server", and the budget test asserts that wording. No command
does that until SW-1980. Use "reload the window" in both until it lands.
S.

### R10. What the test warm-up hides (low; Q5)

Both test changes are sound as tests. `search_time` defaults to 5 s, the
same as `pos::action_options`, so product behaviour is unchanged. Waiting
on `stitchwort/checked` removes a race the product doesn't need to win,
since VS Code asks again when the diagnostics change. But
`fill_for_searches`'s comment states a real cost. Search entries are kept
apart from the checker's (`+nav`), so the first search in a session whose
cache lacks them "checks the whole library from source: over a minute in
the release profile". In VS Code that happens after every change to std,
which on this repo means nearly every rebuild. During that minute, the
default single search worker holds every code action, `contextAt` and dot
completion. With the tests warmed and given 120 s, no test can see it
now. **Change:** measure it in the real server first (cold `+nav`, first
light bulb on an AoC day). If it holds, warm the search entries in the
background after the first check (a lane). The Day 7 ticket's "cold-cache
search slow" may be the same thing: link them.

### R11. Missing tests

- A config read that panics every time (`sources_panic` with
  `usize::MAX`): R2.
- A project whose config parses but `project()` fails: R1. This needs a
  `Faults` switch that makes `Memory::project` return `None`, or a Disk
  test in a temp folder.
- An unattributed panic while reopening (a `give_also` fault): R3.
- The backstop: no test reaches it since SW-2089 (the budget test only
  asserts that "checking after" is absent). For example, three projects
  armed with `usize::MAX`, edited in turn.
- `apply_panic` fires before `edited` runs (`:3180-3184`). So a panic later
  in `apply`, after the suspicion was cleared (in `open_text` or
  `set_text`), isn't covered. Place a second fault point after the `match`.
- Search: R6's test, and a retired project's file closed and opened again
  (it should stay quarantined; that's true by reading, but untested).
- SW-2087 C9's "measure the time to rebuild one AoC project" is still
  undone. R1 to R3 make it matter: the loop rebuilds every open workspace
  15 times.

### R12. Logging a broken config on every lookup (low)

`Disk::sources` prints the parse error each time (`source.rs:115-117`). It
is called by every `quarantine_key` while anything is quarantined, so once
per open document per reopen. Log once per folder and error text, or let
R1's record remove the repeated lookups. S.

## Answers to the brief's questions

1. **Are the earlier findings fixed?** Mostly. See the table below. Two
   are not: C5 has come back through L2's fix (R1), and L1 is fixed only
   for a transient fault (R2).
2. **Budget, retired set and backstop.** Each works on its own terms, and
   the invariant "retired implies quarantined" holds: nothing removes a
   retired key from `quarantined`. They interact badly whenever the key is
   unstable (R1, R2), or when a panic blamed on nobody repeats by itself
   (R3). Then the per-project budget never engages, and the backstop is
   spent at once. A retired project can also come back under another key:
   a symlinked path, or a config edit that moves the file out of
   `sources`. The backstop still bounds that. R1's record narrows the
   first case. The second is arguably right, since a new config deserves
   a retry.
3. **Is the search key complete?** Not quite. It leaves out the other open
   files, the config and the cache (R6), and there is a small race (R7).
   Both only ever cause a null answer, and an edit to the document cures
   it.
4. **State kept twice.** The `Keeper` and the `Checker` agree. `resume`
   destructures the `Keeper`, so a new `Keeper` field can't be dropped
   silently, though a new `Checker` field that ought to be carried
   wouldn't be caught. The real double state is the key: it is stored in
   `quarantined`/`retired`/`suspects`/`budgets`, then worked out again from
   the disk (R1, R2). The per-project `budgets` in the supervisor and
   `retired` in the `Keeper` agree by construction, because the supervisor
   is the only writer of `retired`.
5. **Do the test changes hide slowness?** `search_time` doesn't change the
   product. The warm-up hides a real first-search cost (R10).
6. **Missing tests.** See R11.

## Checked and sound

- `Budget::of` and `spend`: the window and limit arithmetic. A budget
  entry is created only for a panic with a workspace. The budget test's
  count (two for the open, then one per edit, retired at the sixth) matches
  the code.
- D3000: `Open` calls `edited` only when the file's workspace isn't
  quarantined (`:3196-3198`), and the quarantined case falls through to
  `open_text`, which shows the error. The test fails on the old code.
- `retired` is consulted in `edited` before the quarantine is lifted.
  `reopen_documents` forgets retired projects (they are quarantined), and
  `open_text` shows their error.
- SW-2094 L5: `take_keeper` moves the plain fields out before the drop,
  `run` drops the rest under a catch, and `Exit::Closed` takes the same
  path.
- C8: a recovered checker panic is logged once (`tell_recovered`). In
  stopped mode, `Close` clears the error (`close_error`).
- SW-2088: `queue_search` checks the memory before inserting into
  `pending`, so a request answered from memory leaves no pending entry. A
  panic is remembered only if its version is still current. `Close`
  clears the document's entries (`document_moved(None)`). The search side
  has no unattended loop: jobs come only from requests, and memory stops
  the repeats.
- The shared search budget: one `Mutex<Budget>` in `Searches`, and a
  single pop-up (`told_stopped`).
- `sources_hold` is the one rule: `Memory::project` (L6), `home_of` and
  `ProjectWork::holds` (via the trimmed sources) all use it. The misplaced
  doc line is fixed (L3).
- Tests: `a_panic_while_blaming_is_caught_too` fails on the old code (the
  thread died). In `after_an_edit_a_panicked_search_is_tried_again`, the
  second null can only come from the memory. The loose-file test (L4) now
  fails on the old code, through the close and reopen and the pop-up
  count.
- The 1 Nov review (`docs/research/rust-codebase-review.md`): §1.4
  (unbounded search threads, unversioned edits) is still fixed, and these
  merges don't touch it. §4.1's "panicked sessions are discarded" is still
  what the checker and the search workers do, and SW-2091's drop under a
  catch completes it for the checker. Its `NO_ETA` guard point is out of
  scope here.

## Status of the earlier findings

| Finding | Status now |
|---|---|
| SW-2087 C1 (double fault) | **Fixed**, with L5 |
| C2 (one project spends the session's budget) | **Fixed**: per-project budget, retirement, backstop. Undermined when the key is unstable (R1, R2) |
| C3 (light bulb spends the search budget) | **Fixed**: keyed by goal range. Small gaps in the key (R6, R7) |
| C4 (recorded before sent) | Fixed earlier (SW-2086) |
| C5 (two ideas of a workspace) | **Regressed** by SW-2091's `Source::sources` (R1) |
| C6 (per-worker budgets) | **Half fixed**: shared budget, one pop-up. Live workers ignore the stop (R8) |
| C7 (nonexistent command named) | **Fixed** in the pop-ups. The diagnostics still say "restart the language server" (R9) |
| C8 (double log; stopped `Close`) | **Fixed** |
| C9 (test gaps) | **Mostly fixed**. Rebuild time still unmeasured; new gaps in R11 |
| SW-2094 L1 (blame outside the catch) | **Partly fixed**: a transient fault only (R2) |
| L2 (`home_of` reads every file) | **Fixed**, but it caused R1. Logging tail R12 |
| L3 (misplaced doc) | **Fixed** |
| L4 (C5 test can't fail) | **Fixed** |
| L5 (`Keeper` after the drop) | **Fixed** |
| L6 (`MemorySource` copy of the rule) | **Fixed** |
| L7 (`Open` lifts a quarantine) | **Fixed** (D3000) |

## Calls I made

- Counting every panic against the backstop is right (R4): only the
  number and the doc need fixing. Otherwise wrongly attributed panics
  would get fresh budgets.
- R6: clear the whole panicked set on any document change, rather than
  working out which documents a search depends on.
- R5: one pop-up per quarantine and per retirement. The diagnostic carries
  the rest.
- No D questions: everything here is implementation, within D2741, D2980
  and D3000.

## Tickets to file

**Lane 1: one key per open path (Sonnet, 75 min, `crates/lsp`).** R1, R2,
R3, R12, and their tests from R11. Record the key in `open_workspace`, and
in the fallback that `home_of` gives under its own catch. Carry it in the
`Keeper`, consult it first in `workspace_of`, and remove it on `Close`.
Clear `also` after a panic with no workspace. Tests: persistent
`sources_panic`; a project whose `project()` fails (a new `Faults` switch);
a `give_also` fault; the backstop reached. Stay away from SW-2090's files.

**Lane 2: budget arithmetic and messages (Sonnet, 40 min, `crates/lsp`).**
R4, R5, R8, R9. After lane 1 (same function). It could be folded into lane
1 if the time allows.

**Lane 3: panicked-search memory (DeepSeek, 30 min, `crates/lsp`).** R6 and
R7: clear the set on any document change, and insert and clear under the
`versions` guard. A test: a panic at `Demo.sw`, an edit to another open
file of the project, then a search at `Demo.sw` that finds its action.

**Ticket, measure first (no lane yet).** R10: time the first code action
in the real server with a cache that has only the checker's entries, on an
AoC day. If it is over a few seconds, warm the `+nav` entries in the
background after the first check. Link it to the Day 7 "cold-cache search
slow" ticket.
