# How the language server handles failure (SW-1955)

**Status:** proposal, 7 November 2026, Opus. Read-only: nothing was built or
run. Decisions for Matt are D2740 to D2744, plus D2701 and D2733, which are
already open. This note replaces D2730 and gives one plan for SW-1948,
SW-1820, SW-1821, SW-1950 and D2701.

## What this gets the user

Today, one internal error in the checker leaves VS Code looking normal while
the server has stopped checking. Diagnostics freeze at the last check. A
fixed error stays red, a new one never shows, and nothing says why. The only
cure is to guess that the window needs reloading. One internal error in a
proof search turns code actions, `contextAt` and dot completion off for the
rest of the session.

With this plan:

- **An internal error costs a few seconds of checking, not the session.**
  The server notices and starts that part again from the open texts. The
  user gets one notice saying it happened and where the details are.
- **An error that comes back every time doesn't loop.** The project it
  happens in shows one diagnostic, "internal error while checking this
  project; edit a file to try again". Other projects keep working.
- **Editing `stitchwort.yaml` takes effect without a restart**, and a
  project that can't be read says why in the editor, not just in the log.
- **Closing a project's last file frees its memory** (hundreds of MB).

All of these come from one rule and one operation. **The rule:** after a
panic, nothing the panicking code could have touched is trusted again.
**The operation:** drop a workspace's session and build it again from the
open texts. Recovering from a panic, rereading the configuration and
unloading a project all use it.

## 1. The threads, and what each owns

The native server (`serve_from`, `crates/lsp/src/lib.rs:218-296`) has these
threads:

| Thread | Started at | Owns (mutable) | Shares |
|---|---|---|---|
| **Main**: the request loop, `Main::run` | the caller's thread (the CLI's 64 MB mapped thread, `cli/src/main.rs:509`, `host/src/stack.rs`) | `texts` (a `RefCell`, `lib.rs:683`) | `nav` (read), `searches` (mutexes), `cancel`, the two channels |
| **Checker**: `stitchwort-checker` | `lib.rs:250-254` | every workspace's `Work`, so every checking session (`lib.rs:2072-2094`); `versions`, `published`, `announced`, `also` | writes `nav` (`publish`, `lib.rs:2283`), reads `cancel` |
| **Search workers**: `stitchwort-search-N`, one by default (`lib.rs:127`) | `lib.rs:259-271` | the kept session `WARM`, a thread-local (`lib.rs:2953-2955`) | `searches`, `Options::members` |
| **I/O**: `lsp_server`'s reader and writer | `Connection::stdio` (`lib.rs:141`) | the pipes | the channels |

The playground (`Inline`, `lib.rs:2564-2730`) has none of these threads. The
host's worker drives the same `Main` and `Checker` one tick at a time
(`Inline::tick`, `lib.rs:2696`), and a second web worker runs the searches
(`Searcher`, `lib.rs:540-565`; `web/lsp-worker.js:60-113`).

Every unit of work belongs to exactly one thread: a request (main), a
checker step or an edit applied (checker), a search job (search worker).
That makes the policy simple to state per thread.

## 2. What can be trusted after a panic

### The session: never

A checking session is a large mutable object: journal, kernel, caches, and
the namespace in progress. Panics unwind through code that keeps invariants
by save-and-restore pairs without guards. `Machine`'s glue and erasure
switches are one example (SW-1808 finding 4, `core/src/check.rs:1782-1784`
and others). Another is the open declaration that the next `mark` asserts on
(`code-review-driver.md` L7). After a panic, the session may be half-way
through any of these. SW-1808 and the elab review both reached the same
conclusion: such a session must be dropped, not rewound. I agree, and the
rest of this note takes it as given.

### The thread: not either

Dropping the session is **not enough**, because some state lives in
thread-locals, outside any session. I checked every `thread_local!` in
`core`, `elab`, `syntax` and `driver`:

- **Has a drop guard, safe:** `EQUAL_CALLS` (`core/src/reference.rs:768`,
  guard `OpenTrees`, `:790`) and `TREE_MEMO` (`core/src/value.rs:3547`, guard
  `TreeMemo`, `:3616`).
- **No guard, unsafe after a caught panic:** `NO_ETA`
  (`elab/src/unify.rs:1672`). It is set and restored by a bare pair at
  `unify.rs:2030-2032`. A panic inside `unify_in` between the two leaves
  record eta off on that thread for good. Every later unification there
  would then behave differently from a fresh process: a lasting wrong
  answer (an error the user's code doesn't deserve), on a thread whose
  sessions are all new. Confidence high: I read the pair, and nothing else
  resets it.
- **Test-only, statistics, or free lists:** `SHORTCUTS_OFF` (test and
  `reference` builds only), the timing stacks (`elab/src/timings.rs:94-95`,
  only when timings are on), `RUNS`, the `LEAF`/`EMPTY` free-list roots, and
  the syntax stack's low-water mark (`syntax/src/stack.rs:50`). I didn't
  check the last one in depth.

`NO_ETA` can be given a guard; stage 2 does it. The general point remains:
any thread-local mode added later, in any crate, can carry a wrong answer
past a caught panic. Nothing enumerates them, and a test can't find a
missing guard. **A fresh thread is the only boundary that holds for state
nobody has listed yet.** The driver's parallel test runner already does
half of this: it drops its per-thread state after a panic
(`driver/src/driver.rs:129-135`, "A panic may leave the state
half-updated"), but it keeps the thread.

### What is trusted, by thread

| After a panic in | Trusted | Not trusted |
|---|---|---|
| a **request** on main | `texts`, the `searches` maps, `nav`. Requests only read `texts` (the `borrow_mut`s are all in `notified`, `lib.rs:1045, 1065, 1107`); `nav` is read-locked (`lib.rs:1310`), and a panic under a read lock doesn't poison it or change it; the mutexes are each changed in one statement and read through `lock`, which ignores poisoning (`lib.rs:595-597`) | nothing on main. The request itself gets no answer |
| a **notification** on main | (exits; see §3.4) | — |
| a **checker** step or edit | data the checker keeps *about* the client: open texts and versions, focus, what was last published and announced | every session (they share the thread), and the thread itself |
| a **search** job | the `searches` maps; the job's `PendingSearch` | `WARM`, and the thread |
| `nav` after a checker panic in `publish` | each file's entry on its own (it is written file by file, `lib.rs:2293-2331`) | that the files agree with each other. The next publish replaces them; until then hover may mix two checks, each labelled |

## 3. The designs

Three designs are worth comparing. A fourth, Lean's, comes after them.

**A. Exit on any panic.** A panic hook in `lsp` mode exits the process.
VS Code's client restarts it (vscode-languageclient 9.0.1,
`editors/vscode/package.json:12`; by default it restarts 4 times in 3
minutes, then stops with an error; that's from memory, medium confidence)
and reopens the open documents. This is the alternative in D2730.

- For: tiny (about 10 lines), and the trust question disappears: a new
  process is clean.
- Against: every open project is checked again from cold, library load
  included. Searches in flight are lost. A panic that comes back every time
  (the usual kind: the same text panics the same way) crashes 5 times in a
  few seconds, and then VS Code gives up for good. Hover, outline and
  formatting go too, though nothing was wrong with them. The user's message
  is VS Code's generic "server crashed", with no word on which file. It
  also does nothing for the playground or for `Inline` in tests.

**B. Catch, drop the session, continue on the same thread.** Wrap each
checker step and each search job in `catch_unwind`. Drop the affected
workspace's `Work`, or `WARM`. Rebuild it on the same thread.

- For: cheap at run time, since only the affected workspace is rebuilt.
  Small: about 60 lines.
- Against: trusts thread-locals, which §2 shows is wrong today (`NO_ETA`)
  and can't be guaranteed tomorrow.

**C. Catch, drop the thread's work, replace the thread (recommended).**
Each unit of work runs under `catch_unwind`. On a panic, the thread hands
the plain data it keeps about the client to a successor thread, drops
everything else, and ends. The successor builds the sessions again from
that data. A workspace that panics twice in a row without an edit is
*quarantined*: it is not checked, and it shows one diagnostic, until the
next edit to it. Every role has a restart budget. When the budget is spent,
that role stops and says so.

- For: the trust rule is simple and complete. Each piece of data is either
  plain data handed over explicitly, or rebuilt. A repeating panic is
  contained to one workspace, and the user is told where. Hover, outline
  and formatting are unaffected. It is the same shape as the playground's
  recovery (a new worker, documents reopened; `editor-entry.js:202-222`,
  `lsp-worker.js:77-86`), so both editors behave alike.
- Against: about 250 lines. After a checker panic, *every* open workspace
  is rebuilt, not just the one that panicked. Sessions hold `Rc`s and can't
  move to another thread. With the check cache that is mostly replay, and
  panics are rare, so I accept it. I haven't measured the rebuild time;
  stage 3 should.

**D. A process per workspace, as Lean does.** Lean's server is a watchdog
process that starts one `lean --worker` process per open file. When a
worker crashes, VS Code shows "the file worker has crashed" with a "Restart
File" button, and the other files carry on. (That's from memory; I didn't
look it up.) This is the strongest isolation, and it also solves memory: a
project is unloaded by ending its process, which returns everything to the
OS. But the nav answers that hover reads would have to cross a process
boundary, and the whole server would have to be restructured. It is out of
scope here. Design C keeps it possible: C's handover data is exactly what a
watchdog would have to keep.

**rust-analyzer** catches panics per request and answers with an error. That
is safe for it because its analysis database is immutable snapshots
(salsa): a request can't leave a half-changed state behind. Stitchwort's
sessions are mutable, so only the request handlers on main, which only read,
can take that route (§3.4).

**Recommendation: C (D2740).** A's restart loop and lost context hurt most
in exactly the case that matters: a bug that a particular text triggers. B
saves a rebuild at the price of a rule that can't be checked.

### 3.1 The checker

**The problem.** A user's file triggers an elaborator bug. Today the checker
thread dies silently (`lib.rs:250-253`, no catch). Edits go nowhere
(`Main::edit` ignores the send error, `lib.rs:1022`). Diagnostics are frozen.

**The change.**

1. Split `Checker` into a part that can be handed over and the sessions.
   The handover part, `Keeper`, is plain `Send` data:
   - the open documents' texts and versions. This is new:
     `open: BTreeMap<PathBuf, (i32, String)>`. Today the texts live only
     inside the sessions;
   - `also`, `last`, `announced`, `published` and `requests`;
   - the quarantine and the restart budget (below).

   The sessions are the `work` map.
2. `Checker::apply` records an edit in the `Keeper` **first**, then passes
   it on to the sessions. An edit that panics half-way is therefore not
   lost: the successor replays it.
3. The thread's body becomes a supervisor loop. It runs the checker on a
   new thread, takes the `Keeper` and the edits' `Receiver` back when that
   thread reports a panic, and starts a successor with both. Inside the
   checker thread, the catch goes around each `apply` and each `step`,
   *not* around the whole loop. That way the poisoned `work` map is dropped
   by ordinary code after the unwind has finished. A second panic during
   unwinding would abort the process. That case falls back to design A,
   which is acceptable for a double fault.
4. The successor replays an `Open` for each open document, then the focus.
   It republishes as it checks, and the `published` map suppresses the
   unchanged files. `nav` is left as it is until then: hover keeps working
   from the last answers.
5. **Quarantine.** Before each step, the thread notes which workspace it is
   working on, so the supervisor knows where a panic happened (for a panic
   in `apply`: the workspace of the edit's path). Suppose the same workspace
   panics again before any edit to it. The successor then doesn't open it.
   It `forget`s its nav and diagnostics (`lib.rs:2355`) and publishes one
   error diagnostic, at the top of each open file of that workspace:
   `internal error while checking <project>: <panic message>; edit a file
   of the project to try again`. The next edit to one of its files lifts
   the quarantine (one retry per edit, inside the budget).
6. **Budget.** At most 5 checker restarts in 3 minutes, the same as VS
   Code's rule for processes. When it is spent, the checker stops for the
   session. Every workspace is quarantined with a diagnostic, and the
   notice says "checking stopped after repeated internal errors; run
   *Stitchwort: Restart Server*". This follows D2543 (limits fail, never
   choose): a spent budget gives an error, never a stale answer passed off
   as current.

**What it should do, and how we'd know.** With a panic injected in the
first step (§5), the test opens a file, edits it, and receives
`publishDiagnostics` for the new version and `stitchwort/checked`, plus one
`window/showMessage`. With a panic injected in every step of one project,
that project gets the quarantine diagnostic. A second file on its own still
gets its diagnostics.

### 3.2 Search workers

**The problem.** SW-1808 finding 3 / SW-1820: a panic in a search unwinds
out of `search_worker` (`lib.rs:603-613`). The request is never answered.
`searches.running` stays incremented. With one worker, every later search is
answered null at once, because the send fails (`lib.rs:987`).

**The change.** The same as the checker, but simpler, because a worker
keeps nothing worth handing over:

- `catch_unwind` around `job.search.run` in `run_search` (`lib.rs:642`).
- On a panic, answer the request with null through `searched`, so the
  exactly-once rule holds (`PendingSearch::answered`, `lib.rs:579-583`), and
  decrement `running`.
- Then start a successor worker with a clone of the job receiver
  (crossbeam receivers clone) and end this thread. `WARM` was already taken
  out (`lib.rs:2983`), so it is dropped with the unwind, as its comment
  intends. The successor loads the library again on its first project
  search.
- Budget: 5 restarts in 3 minutes. Past that, searches are switched off
  for the session: queued and new ones are answered null, with the notice.
  A search panic that comes back every time costs at most 5 library loads.
- Absorbed from SW-1821 and F9: drop `WARM` explicitly at the end of
  `search_worker`, while the other thread-locals still exist (SW-1808
  finding 8). Set `cancel` on every pending search at shutdown, so `exit`
  doesn't wait for one. The join handles of successor workers go into a
  shared list that `serve_from` joins.

A search's own wrong answer doesn't arise: a search panic produces no
answer at all, and null is "no suggestions", which VS Code shows as an
empty light bulb.

### 3.3 The comparison-level catch (D2701)

`Elaborator::search` catches a panic per candidate and carries on in the
same session (`elab/src/search.rs:1402-1407`; elab review F3). That is
design B inside one request, and it is reachable from the kept session. It
also has the `NO_ETA` hazard: a panic inside a candidate's unification
leaves the thread's record eta off for every later candidate, and, in the
kept session, for every later search.

**Under this policy the catch goes.** A panic ends the unit of work it
belongs to, and only the owner of the unit's state may catch it, because
only the owner can throw that state away. In the editor, the search
worker's catch (§3.2) then answers null and replaces the thread. In the CLI
(`stitchwort search`), the process ends with an internal error; it was
about to end anyway, and one bad candidate shouldn't quietly change the
ranking of the rest. `stats.internal_errors` goes with it. D2701 asked
this for the editor; D2743 asks whether the CLI follows.

Two hardening fixes come along, cheap and worth having even with the catch
gone, since the parallel test runner (`driver.rs:129`) and future code still
catch on a kept thread:

- **`NO_ETA` gets a drop guard.** `ScopedCell` exists already
  (`elab/src/state/mod.rs:117`).
- **`cancellable_at` turns cancel-watching off in a guard**
  (`driver/src/rewind.rs:97-111`; driver review L7). `Machine::reset` also
  clears glue and erasure (SW-1821; core review F10).

### 3.4 The main thread

**The problem.** The main thread answers hover, outline, semantic tokens,
formatting and the rest itself (`Main::answer`, `lib.rs:1308`). Some of
these lex or parse the text. SW-1916's lexer panic is one way in. A panic
there unwinds out of `serve`, through `try_with_stack`'s `resume_unwind`
(`host/src/stack.rs:168`), and ends the process with status 101. VS Code
restarts it: that is design A, by accident.

**The change.** Catch around `Main::request` (`lib.rs:712`). A request
handler only reads main's state (§2), so main is trusted afterwards. Answer
the request with an `InternalError` (-32603) response whose message is the
panic message, unless it was already answered: the searched paths answer
through `PendingSearch`, and the direct path sends only after `answer`
returns. Log it. This is rust-analyzer's policy, and here it is sound for
the same reason: these handlers read but don't change.

Notifications are **not** caught. `notified` changes `texts`, the versions
and the channels in steps. A panic half-way would leave main and the checker
disagreeing about a document's text, which is worse than restarting. Its
code is JSON decoding and map updates, so a panic there is unlikely. If it
happens, the process exits and VS Code restarts it.

### 3.5 What the user sees

| Event | Notice | Editor state |
|---|---|---|
| request panic | logged; the first internal error of the session also gives a notice (D2742) | that request shows nothing; everything else unaffected |
| search panic | the same | that light bulb or completion is empty; the next works (after a library load) |
| checker panic, recovered | the same | diagnostics briefly stale (labelled with their version), then fresh |
| a workspace quarantined | a notice every time, naming the project | one error diagnostic at the top of its open files; its other diagnostics cleared |
| a budget spent | a notice every time | checking (or searching) off; diagnostics replaced by the quarantine diagnostic |

The first-time notice is a `window/showMessage` warning: "Stitchwort hit an
internal error and recovered. Details are in the Stitchwort output; please
report it." The log gets the panic message and its location. A panic hook
that writes to the log is installed once by `serve_from` and chained to the
CLI's broken-pipe hook (`cli/src/main.rs:522-534`). A backtrace is included
when `RUST_BACKTRACE` is set.

A small extension change goes with this: a **Stitchwort: Restart Server**
command (`client.restart()`). Today the extension has only "Show Goals"
(`editors/vscode/package.json:14`), so the only restart is reloading the
window.

## 4. Project load, reload and unload

These aren't panics, but they come down to the same operation, *drop a
workspace and open it again from the open texts*. After stage 3 that is one
function, `Checker::reopen(key)`: `work.remove`, `forget`, then replay the
`Keeper`'s open documents under `key`.

### 4.1 Rereading `stitchwort.yaml` (SW-1950, F7)

**The problem.** The user adds `lib/` to `sources` and opens `lib/A.sw`. The
project is already loaded with the old source list (`open_workspace`,
`lib.rs:2499-2508`), so `A.sw` is checked as a file on its own until the
server restarts. Its imports fail, and its namespace is missing from every
other file's check. Creating `stitchwort.yaml` next to an open file
(`stitchwort init`) has no effect either.

The client already reports the change. VS Code watches exactly
`**/stitchwort.yaml` (`editors/vscode/client.js:36`), and the server
receives `didChangeWatchedFiles`. Then it drops the event: `project_of`
holds only `.sw` files (`ProjectWork::holds`, `lib.rs:2030-2039`), so the
`Edit::Disk` arm finds nothing to do (`lib.rs:2429-2441`).

**The change.** An `Edit::Disk` for a path named `stitchwort.yaml` in folder
`D` reopens:

- the project at `D`, if one is loaded;
- every project whose folder is an ancestor of `D`, since a nested project
  takes files away from it;
- every file on its own under `D`, since it may belong to the project now.

A change to the configuration is rare, so the cost of rebuilding broadly
doesn't matter.

**A project that can't be read.** Today `Disk::project` logs the reason to
stderr and returns `None` (`source.rs:72-80`), or returns `None` without a
log when the YAML doesn't parse (`source.rs:82-85`). The file is then
checked on its own, and the user sees a wall of unknown-name errors. Change
`Source::project` to return `Result<ProjectFiles, String>`. On an error,
open the file on its own as now, but add one error diagnostic at its top:
`the project in <D> can't be read: <reason>`. Put it on `stitchwort.yaml`
too, when that file is open (D2744). The next change to the configuration
retries.

**How we'd know.** A test project in memory has one source folder and an
open file `lib/A.sw` that imports from it. Before the change, the file gets
an unknown-import error. Change the configuration, send
`didChangeWatchedFiles`, and the error is gone. A configuration that doesn't
parse gives the diagnostic.

### 4.2 Unloading a project (D2733, F8)

**The problem.** Browse the AoC days, an example and the roguelike in one
window, and the server keeps three projects' sessions (hundreds of MB each)
until exit. `Edit::Close` drops only a file on its own (`lib.rs:2400-2414`).
`next_key` also keeps checking projects nobody has open.

**The change.** When a project's last open file closes, start a grace
period of 60 seconds. If no file of it is opened in that time, `forget` it
(its diagnostics are cleared) and drop its `Work`. Reopening is a normal
open. The check cache makes that a replay of what was checked, not a
re-check. The grace period covers the common "close a tab, open the next
file of the same day" case. A checker that is idle needs a timeout on its
`recv` to notice that the grace period has ended (`lib.rs:2127`). The
checker already uses `recv_timeout` for the debounce, so this is a small
change.

The user-visible cost: a project's errors leave the Problems panel when its
last file has been closed for a minute. I think that is right, because
nothing updates them any more: files can change on disk, and they would go
stale. D2733 asks it.

**How we'd know.** With the grace period set to zero, in a test option, close
the last file. The test then receives empty `publishDiagnostics` for every
file of the project, and the checker's workspace count drops to zero. That
needs a test probe, as `Options::journal` is today.

### 4.3 Found on the way: `.sw` files changed on disk are never seen

Because the client watches only `stitchwort.yaml` (`client.js:36`), the
server never hears about changes to project files that aren't open. Branch
switches, `stitchwort fmt` and edits in another tool all go unseen. The
`Edit::Disk` arm for `.sw` files (`lib.rs:2429-2441`) is unreachable from
VS Code. A file opened later is read fresh, but the *other* files of the
project keep the text they had when the project was loaded. Confidence
medium-high: I read the client and the server, but didn't run them. The
fix is to watch `**/*.sw` as well, either in the client or by registering
the watcher from the server. I suggest filing it on its own.

## 5. Testing

**A seam, not a feature flag.** I decided on an always-compiled field,
`Options::faults: Arc<Faults>` (`#[doc(hidden)]`), rather than a cargo
feature. Its atomics say "panic at the Nth checker step", "panic in the Nth
search", "panic in requests named M" and "panic when checking a workspace
whose path contains S". The threaded tests live in the CLI's test binary
(`crates/cli/tests/server/lsp.rs:28-60`). A feature turned on from there
would build `lsp`, and so `cli`, twice: once for tests and once for the
binary. That costs dev-loop time on every change. The field costs one
relaxed load per step or job, which is nothing next to a namespace check.
With no faults set, nothing changes.

The tests use the threaded server (`Client::start_with`), not `Inline`,
because the recovery lives in `serve_from`:

1. `checker_recovers_after_a_panic`: panic at step 1. Then the
   diagnostics for the next edit arrive, `stitchwort/checked` follows, and
   exactly one `showMessage` was sent.
2. `a_repeating_panic_quarantines_its_workspace`: a project that always
   panics, and a file on its own that doesn't. The project gets the
   quarantine diagnostic, and the file gets its usual diagnostics. After an
   edit to the project, it is tried once more.
3. `the_checker_budget_stops_checking`: 6 panics, then the stop
   diagnostic. Hover still answers.
4. `a_search_panic_is_answered_and_the_next_search_works`: the first code
   action panics and is answered null; the second gets its actions. This
   is SW-1808's test 4 and D2584.
5. `a_request_panic_is_an_internal_error`: hover with a fault gets -32603,
   and the next hover works.
6. `a_new_source_folder_is_picked_up` and `a_broken_config_is_a_diagnostic`
   (§4.1).
7. `a_closed_project_is_unloaded` (§4.2), with the grace period at zero.

Each needs the library loaded once, through the test standard library
cache. I'd expect 1 to 3 s each, but I haven't measured. They run as
`task test:one -- -E 'binary(server) & test(/^lsp::/)'`, filtered by name.

## 6. The playground

**What it does now.** A panic in wasm traps, because `wasm32-unknown-unknown`
can't unwind and the build sets nothing else (`web/build.sh:7`). The
instance can't be trusted afterwards, which is §2's rule at the instance
level. `lsp-worker.js` posts `crashed` (`:139`, `:184`, `:199`), and the
page starts a new worker. It gives that worker the projects, and the client
reopens its documents (`editor-entry.js:202-222`). A crashed search worker
is ended, its search answered null, and a new one started for the next job
(`lsp-worker.js:77-86`). That is design C already, with a web worker as the
unit instead of a thread.

**What changes, so that both editors behave alike:**

- The page's checker budget is "more than 3 restarts, ever"
  (`editor-entry.js:206`). It should be the same 5 in 3 minutes, so a long
  session with unrelated crashes isn't stopped for good. The search worker
  has no budget at all; it should get the same one.
- The notices should use the same wording as natively (§3.5).
- Quarantine, as an option. The page can't tell which workspace trapped. If
  `Inline` exposed the workspace its next tick will check, the page could
  pass it to the new worker as `quarantine`, and a crash that comes back
  every time would be contained there too. That is for later, and low
  priority. I've left it out of the stages.
- `Inline` gets no catch. In wasm a catch can't run. Natively, `Inline` is
  only a test harness.

## Questions for Matt

- **D2740:** When the language server hits an internal error (a panic) in
  the checker or a proof search, should it recover inside the process, by
  replacing the thread that panicked and rebuilding its sessions from the
  open texts, rather than exiting so that VS Code restarts it? This
  replaces D2730. [rec: yes, recover. Exiting loses every project's check,
  and an error that comes back every time hits VS Code's 5-crash limit in
  seconds and leaves no server at all. A fresh thread is the only boundary
  that clears thread-local state, which `NO_ETA` shows can carry a wrong
  answer past a caught panic.]
- **D2741:** When the same project panics again before any edit to it,
  should the server stop checking that project and show one "internal
  error" diagnostic in its open files until the next edit, with an overall
  budget of 5 restarts in 3 minutes, after which checking stops for the
  session with a message? [rec: yes. It contains a repeating bug to one
  project and turns a spent budget into an error, never a stale answer
  (D2543).]
- **D2742:** For an internal error the server recovered from, should the
  user get a pop-up the first time in a session (and only a log entry after
  that), rather than a pop-up every time, or only a log entry? [rec: the
  first time only. It is a bug worth reporting, but the editor works, and
  repeating the pop-up would nag. A quarantine or a spent budget always
  gets one.]
- **D2743:** Should the catch per comparison in `search.rs:1402` go for the
  CLI's `stitchwort search` too, so that a panic there ends the command with
  an internal error instead of skipping one candidate and carrying on in
  the same session? (D2701 asked this for the editor; my recommendation
  there is yes.) [rec: yes. One rule everywhere: only the owner of the
  state catches, and the owner throws the state away.]
- **D2744:** When a folder's `stitchwort.yaml` can't be read, should the
  open files show an error diagnostic giving the reason (and keep being
  checked on their own), rather than only a line in the output log?
  [rec: yes. Today the user sees unknown-name errors with no hint of the
  cause.]
- **D2733** (open) now reads: unload a project 60 s after its last file
  closes, clearing its diagnostics. [rec: yes.]

Decided here, as implementation detail: the fault seam is an `Options`
field, not a cargo feature (§5). The budget is the same for every role. A
reread of the configuration reopens broadly. The grace period is 60 s. The
order of the stages.

## Tickets to file

In order. Stages 1 and 2 can run side by side. Stages 4 and 5 both touch
`Checker::apply`, so they run one after the other.

1. **Fault seam, search worker recovery, request catch** (Sonnet, 75 min).
   This adds `Options::faults`. §3.2: catch in `run_search`, answer null,
   start a successor, the restart budget, `WARM` dropped explicitly, cancel
   at shutdown. §3.4: catch per request, `InternalError`. The log hook.
   Replaces **SW-1820** (with D2584) and absorbs SW-1821's finding 8 and the
   review's F9. Tests: the new tests 4 and 5;
   `searches_in_a_row_give_what_fresh_ones_do`;
   `task test:one -- -E 'binary(server) & test(/^lsp::/)'` filtered to the
   search and shutdown tests.
2. **One catch policy in the elaborator, and its guards** (Opus, 45 min:
   unifier and kernel state). Remove the `search.rs:1402` catch (D2701,
   D2743). Give `NO_ETA` a guard. `cancellable_at` gets a drop guard (L7).
   `Machine::reset` clears glue and erasure. Absorbs the rest of
   **SW-1821**, and the elab review's F3. Tests: `task test:lane
   AREA=search`, `task test:lane AREA=core`, and the driver's rewind tests
   (`task test:one -- rewind`).
3. **Checker recovery** (Sonnet, 90 min; Opus if it stalls). Split out
   `Keeper` with the open texts. Record before applying. The supervisor and
   successor thread. Replay. Quarantine and budget. The notices.
   `Checker::reopen`. Measure the time to rebuild one AoC project. Replaces
   **SW-1948** (D2740 to D2742). Tests: the new tests 1 to 3, and the
   existing threaded `lsp::` tests for diagnostics and `stitchwort/checked`.
4. **Reread the configuration, and project errors in the editor** (Sonnet,
   60 min, after 3). §4.1: `Source::project` returns `Result`, the
   diagnostics (D2744). The first half of **SW-1950** (F7). Tests: new
   test 6, `task test:lane AREA=lsp`.
5. **Unload closed projects** (Sonnet, 45 min, after 3). §4.2, D2733. The
   second half of **SW-1950** (F8). Tests: new test 7, `task test:lane
   AREA=lsp`.
6. **Extension: a Restart Server command, and watch `**/*.sw`** (DeepSeek,
   30 min, any time). §3.5 and §4.3. The server side of the `.sw` events
   already exists; check it with one threaded test that changes an
   unopened project file on disk. Tests: `editors/vscode/test/client.test.js`
   (it pins `watchedGlob`) and that test.
7. **Playground: the same budget and wording** (DeepSeek, 30 min, after 3).
   §6: a windowed budget for both workers, and the shared notice text.
   Tests: the playground's crash and restart test, if it has one; otherwise
   add a JS unit test of the budget.

Not covered here: SW-1916's lexer bug itself (stage 1 only contains it); the
kept session's leaks (SW-1818/SW-1937, SW-1819), which don't fail but grow;
F10's erased cancellation; and process isolation (design D), which is a
possible later direction, not a plan.
