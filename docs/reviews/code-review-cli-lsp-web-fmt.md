# Code review: `cli`, `lsp`, `web`, `fmt`, `bench`, `partial-model`, `standalone`, `host` (SW-1924)

**Status:** review by reading only, 7 November 2026, Opus. Nothing was built
or run, so every claim about behaviour comes from the code and carries a
confidence. Most of the time went on `crates/lsp/src/lib.rs` (read in full
apart from navigation helpers) and `crates/cli/src/main.rs` (commands, exit
codes, `test --json`, `run --profile`, `fmt`, the search commands); then
`crates/web` (`lib.rs` in part, `lsp.rs`, the two workers in `web/`),
`crates/fmt` (`lib.rs`, `check.rs`, the fallbacks in `layout.rs`),
`crates/bench` (`alloc.rs`, the examples benchmark, `main.rs`),
`crates/host` and `crates/standalone` in full. `partial-model` got a skim:
it is a test oracle, not shipped code.

This review builds on, and doesn't repeat,
[SW-1808-kept-search-session.md](SW-1808-kept-search-session.md) (the kept
search session: leaks, a panic killing the search worker, cancellation;
SW-1818 to SW-1823), the two syntax reviews
([code-review-syntax.md](code-review-syntax.md),
[code-review-syntax-opus.md](code-review-syntax-opus.md): the lexer panic on
the server's main thread, SW-1916, and the formatter's quadratic tree
comparison) and [code-review-driver.md](code-review-driver.md) (editor
freshness, SW-1922).

## Summary

The user-facing crates are in good shape. The 1 November finding is fixed
properly: proof searches, `contextAt` and dot completion run on a bounded
pool (one worker by default), every search records the document version it
was computed from and is answered with null if the document moved on, a newer
request supersedes an older one, `$/cancelRequest` is answered with
`RequestCancelled`, and edits are versioned (`documentChanges`) when the client
supports them. Each of these has a test. Exactly one response goes out per
request (`PendingSearch::answered`). Diagnostics are labelled with the version
of the text that was checked. The formatter is the most defensive component in
the tree: it refuses broken files, falls back per declaration, and checks
tokens, comments and the syntax tree before returning. The playground restarts
a crashed or stale worker cleanly. The standalone runtime and the host's
terminal and stack code are careful and well argued.

What is left falls into three groups. (1) **One staleness hole remains in code
actions:** the goal's range comes from the last *published* check, but the
edit is labelled with the *current* version, so a versioned client applies it
to text that has moved (F1). (2) **A panic in the checker thread leaves a
server that looks alive but never updates diagnostics again** (F2). This is
the checker-side twin of SW-1820, and probably the worst failure a user can
hit. (3) **Small CLI problems:** `check` and `audit` of several files keep
every file's session alive (F3), `stitchwort fmt DIR` walks hidden folders and
follows symlinks, which reaches `.claude/worktrees` and loops on a cycle (F4),
and the `--json` modes don't always print JSON (F5, F6; SW-1692 is still
open).

**Top five recommendations**

1. **Recover from a checker panic** (F2): catch it per step, drop that
   workspace's session and build a fresh one, and tell the user with
   `window/showMessage`; or exit, so the client restarts the server (D2730).
2. **Take a code action's goal range from the current text** (F1): use the
   client's goal diagnostic in `context.diagnostics` (the client shifts it
   with edits), or check that the current text has the `?` at the range;
   otherwise answer with no action.
3. **One JSON object on stdout for every `--json` run** (F5, F6, SW-1692):
   load failures included, `ok` true exactly when the exit status is 0, and
   `--verify-cache`'s line moved to stderr (D2732).
4. **`stitchwort fmt DIR`: skip hidden folders, don't follow symlinked
   folders, write atomically** (F4; D2731).
5. **Free each file's session in `check`/`audit` of several files** (F3); and
   look into the step counts in the examples benchmark that differ by thread
   placement (F13). Those differences may be an address-keyed table in the
   compiler.

**Counts:** 1 high, 7 medium, 14 low.

## Findings

| # | Where | What | Sev. | Conf. | Fix |
|---|---|---|---|---|---|
| F2 | `lsp/src/lib.rs:250-253, 291-293, 1021-1025, 2215-2279` | A panic in the checker thread kills it silently: the main thread keeps answering from stale answers, edits go nowhere, diagnostics never update, and the client doesn't restart a server that is still running | high | high | M |
| F1 | `lsp/src/lib.rs:746-755, 782-790`; `driver/src/search_at.rs:193-195`; `driver/src/at.rs:518-526` | A code action's goal range comes from the last published check (and `goals_kept` keeps old places on purpose), but the edit is labelled with the document's current version; the search picks the nearest `?` on that line in the new text, and the edit replaces the old range | medium | medium-high | S |
| F3 | `cli/src/main.rs:1145-1169, 2500-2512, 1304-1311` | `check a.sw b.sw …` and `audit` of several files `mem::forget` each file's session inside the loop: memory grows by a session per file | medium | medium | S |
| F4 | `cli/src/main.rs:2811-2831, 2848` | `fmt DIR` recurses into every folder, hidden ones included (`.git`, `.stitchwort`, `.claude/worktrees`), and follows symlinked folders (a cycle never ends); files are rewritten with a truncating `fs::write` | medium | high | S |
| F5 | `cli/src/main.rs:1427-1454, 1467-1504, 1511-1559, 1365` | `test --json`: nothing on stdout when the file or project doesn't load; `ok` ignores open goals and cache disagreements (SW-1692); `--verify-cache` prints a text line on stdout after the JSON | medium | high | S |
| F7 | `lsp/src/lib.rs:2499-2508, 2429-2441`; `lsp/src/source.rs:64-91` | The server never rereads `stitchwort.yaml`: a source folder added later, or a project made while a file is open, is checked as a lone file until restart; a project that can't be read falls back to file mode, with the reason only in the log | medium | medium | M |
| F13 | `bench/src/lib.rs:144-157`; `bench/baseline.toml:3-4` | The examples benchmark's *step* counts vary between runs with thread placement ("as if something depended on where the heap puts things"); the tolerance hides it, and the baseline header still says the counts are deterministic | medium | low | M (investigate) |
| F8 | `lsp/src/lib.rs:2400-2415` | A project's session is never dropped, even when its last open file closes: each project opened in an editor session holds its memory until exit | medium | high | S-M |
| F6 | `cli/src/main.rs:2289-2293, 2338-2348, 2368, 2376-2378` | `search --json` and `search --at --json` print `{"version":1,"error":…}` for a search error, but nothing on stdout for an unreadable file, a project that doesn't analyse, or a library that doesn't load | low | high | S |
| F9 | `lsp/src/lib.rs:284-290` | Shutdown joins the search workers without cancelling the running search: `exit` waits for it (a file's search ignores cancellation anyway) | low | high | S |
| F10 | `driver/src/rewind.rs:102`; `lsp/src/lib.rs:1021-1025, 2135-2157` | The cancel flag is cleared at the start of each check, after the edits are drained: an edit that arrives in between has its cancellation erased, so the old text's check runs to the end | low | medium | S |
| F11 | `host/src/stack.rs:118-170`; `host/src/lib.rs:31-37` | Every `stitchwort` command runs on a thread made with `pthread_create`, which std gives no alternate signal stack: a stack overflow there ends with a bare `SIGSEGV`, not Rust's "has overflowed its stack" | low | medium | S |
| F12 | `bench/src/alloc.rs:92-98, 142-145` | Worker threads switch the global count back on when they stop measuring; their thread-local work lists (`term.rs:267`, `value.rs:419`), grown while it was off, are then freed against `LIVE`, which drifts down (a `usize`, so it can wrap) | low | medium | S |
| F14 | `fmt/src/check.rs:63-87` | The comment check compares comments in order but not which token each is attached to: a comment that moves past a token is not caught (harmless today; the tree check doesn't see comments) | low | medium | S |
| F15 | `fmt/src/check.rs:29-33` | `same_text` accepts any two multi-line tokens; the doc says "with the same value", which only the tree check ensures | low | high | S |
| F16 | `lsp/src/arms.rs:80-103, 107` | `split_target` uses the LSP column (UTF-16 units) as a `char` index, and hands back `char` columns as an LSP position: off by one per astral character before the cursor | low | high | S |
| F17 | `lsp/src/lib.rs:1452-1459` | `stitchwort/tests` reads unopened files with `std::fs`, not the `Source`: the playground's Testing panel sees open files only | low | high | S |
| F18 | `web/src/lib.rs:664-669, 55-60` | Native tests of `web` override the session limits (1.5 MiB of stack budget) where the wasm build uses 256 KiB; the comment above says no caller sets them differently | low | high | S |
| F19 | `cli/src/build.rs:503-512` | `TempDir::new` uses a guessable name under the shared temporary folder and `create_dir_all`, which succeeds on a folder someone else made | low | medium | S |
| F20 | `cli/src/search_log.rs:33-43` | `private_path` keeps a relative path as given, so `../../home/x/goals.sw` names a folder outside the one the command ran in (against SW-993's test) | low | high | S |
| F21 | `cli/src/main.rs:1134-1142` | `check` usage errors (files and names mixed, `--index` with several files) exit 1, where other commands' usage errors (and clap's) exit 2 | low | high | S |
| F22 | `lsp/src/lib.rs:3091-3098` | The dot-completion cache key covers the open files' text but not files on disk: a change to an unopened project file leaves the cached members until the document changes | low | medium | S |

## Details

### F2. A checker panic leaves a server that looks alive (high; confidence high)

The checker thread (`serve_from`, `lib.rs:250-253`) runs `Checker::run` with
no `catch_unwind`. A panic anywhere in a step (the elaborator, `live`, the
answers, the publication) unwinds and ends the thread. Nothing notices until
shutdown: `Main::edit` ignores the send error (`let _ =
self.to_checker.send(edit)`, `lib.rs:1022`), and the join at `lib.rs:291` runs
only after `exit`. The main thread keeps serving hover, definition,
completion and the rest from the last published answers. Search workers are
separate, so code actions still work.

**What the user sees:** the panic's message in the extension's output log
(which most users never open), then an editor whose diagnostics are frozen at
the last check. New errors don't appear, fixed ones don't go, and
`stitchwort/checked` is never sent again. The process doesn't exit, so VS
Code's client doesn't restart it. The user has to guess that they should
reload the window.

This matters because a panic in the checker is the general case of a bug
anywhere in the front end, not one bug: SW-1916's lexer panic is one (on
the main thread, which at least kills the process), and the elaborator and
kernel are much larger. Natively the checker has a 64 MB stack and limits
guards, so this is about panics, not overflow. In the browser a trap already
restarts the worker (`web/editor/src/editor-entry.js:183`), so only native
is affected.

**Fix (M):** wrap `Checker::step` in `catch_unwind`. On a panic, treat the
workspace's session as poisoned (SW-1821 explains why a session after a
caught panic can't be trusted): remove the `Work` entry, `forget` its
published answers, send `window/showMessage` ("internal error while checking
X; checking it again from scratch", with the panic message), and reopen it
from the open texts. If the same workspace panics again on unchanged text,
stop retrying and say so, instead of looping. The simpler alternative is a
panic hook in `lsp` mode that exits the process, which the client restarts
(up to 5 times in 3 minutes in VS Code): small, but every open file's check
starts again from cold. D2730. Combine with SW-1820, the search worker's
version of this.

**Test:** a test-only `Options` hook that panics in the Nth step; check that
diagnostics for a later edit still arrive, and that a message was shown.

### F1. Code actions can replace the wrong range (medium; confidence medium-high)

`Main::code_action` finds the goal from `nav.goals` (`lib.rs:746-755`), which
the checker writes when it publishes (`lib.rs:2304-2316`). That is the goal's
range in the text of the *last check*. `queue_search` then reads the
document's *current* version (`lib.rs:970`), and the search runs on the
current text with the old range. It finds the goal by line and the column
nearest to the old one (`search_at.rs:193-195`), but the edit replaces the
old range (`at.rs:518-526`, `code_actions` at `lib.rs:3170-3194`) and is
labelled with the current version. A client that applies versioned edits
checks the version, sees that it matches, and applies the edit.

**Scenario:** `theorem t … := ?` is checked and published. The user puts the
cursor on the `?`, types one character earlier on the same line (version 6),
and opens the light bulb before the debounce and recheck have finished. A
project's check takes a second or more, so the window is long. VS Code asks
for code actions with version 6. The server takes the goal's version-5
range, finds the shifted `?` (the nearest on the line), searches, and returns
"Replace ? with `rfl`" with an edit that replaces version 5's range, now the
character before the `?`, tagged version 6. Accepting it deletes the wrong
character and leaves the `?` behind. Kept goals (`goals_kept`) widen the
window: while the stretch around a goal doesn't parse, its published range
stays at its old place on purpose, so any typing earlier in that stretch
moves it.

**Fix (S):** take the range from the client's own goal diagnostic in
`p.context.diagnostics` (`is_goal` already exists). VS Code moves diagnostic
ranges as the text is edited, so that range is in the current text. Also,
before queueing, check that the current text has `?` at the range, and
answer with no action otherwise. Defence in depth: have the search return
the chosen goal's position, and drop the result when it differs from the
range.

**Test:** with `search_delay`, publish, then change the text so that the `?`
moves along its line (version 2), then request a code action at the new
place. The edit must replace the `?` in version 2's text, or there must be
none.

### F3. `check` and `audit` of several files keep every session (medium; confidence medium)

`discard` (`main.rs:1304-1311`) forgets a session, because "the process is
about to exit". In `check` with files (`main.rs:1145-1169`) and `audit` with
files (`main.rs:2500-2512`), it is called inside the per-file loop, so every
file's session, its library and checked terms included, stays allocated
until the process ends. The language server's measurements put a session
with the library loaded at about 0.45 GB (`lsp/src/lib.rs:2961`). A CLI
file session that replays only what the file imports is smaller, but `check
examples/accept/*.sw` (hundreds of files) still grows by a session per file,
in GB.

**Fix (S):** `drop` the session in the loop, except after the last file, or
keep one session and rewind it to a mark taken after the library is loaded,
as `search_session` does. Update `discard`'s comment.

### F4. `fmt DIR` walks too much and writes in place (medium; confidence high)

`sw_files_in` (`main.rs:2811-2831`) recurses with `path.is_dir()`, which
follows symlinks, into every folder:

- **Hidden folders:** `stitchwort fmt .` at this repository's root formats
  every `.sw` file under `.claude/worktrees/*`, which are other lanes'
  checkouts, and under `.stitchwort/` or a vendored copy anywhere below.
  `git` and `rustfmt` users expect a folder argument to mean "my sources".
- **Symlink cycles:** a link back to a parent recurses until the stack
  overflows, or for ever across many links.
- **Unreadable folders** are skipped silently (compare SW-1920).

`format_file` writes with `std::fs::write` (`main.rs:2848`), which truncates
and then writes, so an interrupted write (disk full, a signal, a crash)
leaves a truncated source file.

**Fix (S):** skip entries whose name starts with `.`, use
`entry.file_type()` (which doesn't follow links) and don't follow symlinked
folders, report unreadable folders, and write each file to a temporary file
in the same folder and then rename it. D2731.

### F5. `test --json` isn't always JSON (medium; confidence high)

- When the file or project doesn't load (`main.rs:1427-1429, 1467-1469`) the
  command returns exit 1 with nothing on stdout: a consumer that parses
  stdout gets an empty document. The extension's Testing panel and any CI
  script have to treat "no output" as a separate case.
- `ok` (`main.rs:1556-1557`) is computed before the open goals and the cache
  verification are counted (`main.rs:1433-1454`): with goals open, the
  output says `"ok": true` and the exit status is 1. This is SW-1692, still
  open.
- With `--verify-cache`, `verified` prints `verified the cache: …` with
  `println!` (`main.rs:1365`) after the JSON object, so stdout is no longer
  one JSON value and `jq` fails.

**Fix (S):** in JSON mode, always print exactly one object: on a load
failure `{"ok": false, "error": {"code", "message"}, "diagnostics": […]}`, as
`search --json` does for its errors. Compute `ok` after goals, `--only`
matching and verification, so `ok` is true exactly when the status is 0.
Send `verified`'s summary to stderr in JSON mode, or add it as a field.
Decide the contract once for every `--json` command (D2732); F6 is the same
question for `search`.

### F7. Project configuration is read once (medium; confidence medium)

`Checker::open_workspace` (`lib.rs:2499-2508`) loads a project only if its
folder isn't in `work` yet. `ProjectWork::sources` comes from
`stitchwort.yaml` at that moment, and nothing reloads it: `Edit::Disk` for
`stitchwort.yaml` is dropped because `project_of` doesn't hold it
(`lib.rs:2429-2441`). Consequences:

- Add `lib/` to `sources` and open `lib/A.sw`: the project is already in
  `work`, so the file is opened as a file on its own. Its imports of the
  project fail, and its namespace is missing from every other file's check,
  until the server restarts.
- Open a file, then create `stitchwort.yaml` next to it (`stitchwort init`):
  the file stays in single-file mode.
- A project that can't be read (`Disk::project` returns `None` after logging
  to stderr, `source.rs:72-80`; a config that fails `parse_config` returns
  `None` without even a log, `source.rs:82-85`) falls back to checking the
  open file on its own. The user sees a wall of unknown-name errors, and the
  real reason is only in the output log.

**Fix (M):** watch `stitchwort.yaml` (the client's `didChangeWatchedFiles`
registration) and, on a change, drop the project's `Work` and open it again
from the open texts. Turn a project that can't be read into a diagnostic on
the open file ("the project in X can't be read: …") or a `showMessage`.

### F13. Step counts that depend on thread placement (medium; confidence low)

`Counts::close_to` (`bench/src/lib.rs:144-157`) accepts a difference of one
part in 100,000 because "a few examples, in 1,498, take a few dozen steps
more or fewer, as if something in them depended on where the heap puts
things, which another thread's allocations change". Allocation counts and
peaks can reasonably vary with buffer growth. *Steps* are evaluator work,
and they should depend only on the program. If the number of steps an
example takes depends on heap addresses, then something in checking does
too: an address-keyed table such as a cache keyed on `Rc::as_ptr`, or a hash
of an address that decides an order. An address cache whose key can be
freed and reused is a wrong-answer risk (a false hit), not just noise. This
is category (1) of the brief, and the tolerance hides it.

The baseline's header (`bench/baseline.toml:3-4`) still says the counts are
"the same on every run". The job count, which the counts depend on
(`main.rs:36-40`), isn't recorded in the baseline, so a run with `--jobs 4`
is compared with a baseline taken at 8 without a warning.

**Fix:** an Opus investigation (M). Run the examples benchmark twice with
`--parts` and compare the per-part steps. For an example that differs, run
it alone under two allocators, or with a few allocations padded in front, to
show that the difference follows addresses. Then find the pointer-keyed
structure (`grep` for `as_ptr`, `addr`, `ptr::eq` in hashed keys in `core`
and `elab`). Separately (S): record `jobs` in the baseline and refuse to
compare different values, and correct the header.

### F8. Projects are never unloaded (medium; confidence high)

`Edit::Close` removes a file-on-its-own's `Work` and its answers
(`lib.rs:2402-2406`), but a project's file only goes back to its disk text
(`lib.rs:2408-2414`). The project's `LiveProject`, with its session, stays in
`work` for the life of the server. Browse three projects in one window (the
AoC days, an example, the roguelike) and the server holds three sessions of
hundreds of MB each, plus a search worker's kept session (0.45 GB). Recheck
work also continues for projects nobody is looking at, because `next_key`
picks any workspace with pending work.

**Fix (S-M):** when a project's last open file closes, drop its `Work` and
`forget` its answers. To soften reopening, keep the most recently closed one
for a minute. D2733, since it trades memory against the time to reopen a
project.

### F6. `search --json` early errors print no JSON (low)

`search` and `search --at` print a JSON error object when the search itself
fails (`main.rs:2410-2418`, `2209-2217`). The earlier exits, for a file that
can't be read (`2289-2293`), a project that can't be listed or analysed
(`2338-2348`), a `--project` that isn't one (`2368`), or a library that
doesn't load (`2376-2378`), return 2 with only stderr. Same fix as F5.

### F9. Shutdown waits for a running search (low)

`serve_from` stops the checker with its flag, then drops `main`
(`lib.rs:284-290`), which closes the job channel. Workers finish the job
they are running before they see the channel closed, and the join waits for
them. No pending search's `cancel` is set. A file's search doesn't watch its
flag (SW-1820), and a project's first search loads the library. So `exit`
can take the search's whole time limit (5 s) plus a load. **Fix:** at the
end of `Main::run`, set `cancel` on every entry of `searches.pending`.

### F10. An edit's cancellation can be erased (low)

`Main::edit` sends the edit and then sets the flag (`lib.rs:1022-1024`).
`Session::cancellable_at` clears the flag when a check starts
(`rewind.rs:102`). The checker drains the channel and then steps
(`lib.rs:2135-2157`). If an edit arrives after the drain and its flag is set
before `cancellable_at` clears it, the clear erases it. The step for the
older text then runs to the end, and its answer is published, correctly
labelled with the older version, before the new edit is applied. The
window is short with a debounce, and wider with `debounceMs: 0`. Nothing
wrong is shown; only the new answer is delayed. **Fix:** clear the flag in
`Checker::run` before draining the channel, and have `cancellable_at` only
read it. That is in the driver, so coordinate with SW-1922.

### F11. Stack overflow on the mapped thread is a bare SIGSEGV (low)

`try_with_stack` maps its own stack and starts the thread with
`pthread_create` (`stack.rs:118-170`), because std's thread library would
account a 64 GiB native stack on Linux. Every command runs there, through
`main.rs`'s `try_with_stack(STACK, …)`, including the language server's main
thread. std installs its stack-overflow handler's alternate signal stack
only on threads it starts. On this thread, an overflow into the guard page
(`GUARD`) can't run the handler, and the process dies with a bare `SIGSEGV`
(exit 139). The usual "thread … has overflowed its stack" and `SIGABRT` don't
appear. The depth guards make overflow rare, but when it happens the report
looks like memory corruption. **Fix (S):** use `std::thread::Builder` for
ordinary sizes (the CLI's 64 MB) and keep the mapping for native-run sizes,
or install a `sigaltstack` in `start` (that needs unsafe code, and an Opus
review).

### F12. The bench's global count drifts (low)

`measure_this_thread(false)` (`alloc.rs:142-145`) sets `GLOBAL` back to
true. The worker's thread-locals that grew while it was false, the work lists
`FREEING` (`core/src/term.rs:267-272`) and `PENDING`
(`core/src/value.rs:419-425`), are freed when the thread exits. `dealloc`
then subtracts them from `LIVE` (`alloc.rs:92-98`) although they were never
added. `LIVE` is a `usize`, so it drifts down and could wrap. The examples
benchmark runs first, so every later benchmark in the process measures
against a drifted `LIVE`. Peaks are differences, so they stay right unless
`LIVE` crosses zero. **Fix (S):** leave `GLOBAL` off for the rest of a
worker's life, or make `LIVE` signed. Also: the doc comment for
`ALLOCATIONS` sits above `GLOBAL` (`alloc.rs:23-29`, two comments merged),
and `--parts` write errors don't change the exit status (`main.rs:110-113`).

### F14, F15. The formatter's comment and token checks (low)

`same_comments` (`check.rs:63-87`) flattens every token's leading and
trailing comments into one list and compares the lists. A comment that moves
from before a token to after it passes. The tree check can't catch that,
because the AST has no comments. Today the layout only changes whitespace
between tokens, so a comment can't pass a token, and this is a gap in the
safety net, not a bug. **Fix:** compare per-token trivia (the token lists
match apart from commas and parentheses, so pair them by index after
stripping). `same_text` (`check.rs:31-33`) treats any two multi-line tokens of
the same kind as equal. That is safe only because the tree check compares
literal values. Say so in the comment instead of "with the same value".

### F16 to F22 (low)

- **F16:** `arms::split_target` indexes `chars` with the LSP `character`,
  which counts UTF-16 units, and returns `char` columns that `with_context`
  then treats as LSP columns. A line with an emoji or another astral
  character before the cursor is off by one. Convert at the boundary.
  `text.lines()` also turns `\r\n` into `\n` in the replaced arm.
- **F17:** `stitchwort/tests` (`lib.rs:1452-1459`) reads unopened files with
  `std::fs::read_to_string`. Use `self.text(uri)`, which goes through the
  `Source`.
- **F18:** `web/src/lib.rs:664-669` overrides the limits under `cfg(test)`,
  so native tests of the playground's API check with the 2 MiB thread's
  budget (1.5 MiB), not the 256 KiB that wasm sessions use (from
  `Options::new(guard + 256 KiB)` through `session_for`). The comment at
  `lib.rs:55-58` says no caller sets them differently. Either run the tests
  with the wasm guard (and a thread sized for it), or say why not.
  `lsp::options` and `search_options` (`web/src/lsp.rs:170-182`) are the
  same function twice.
- **F19:** `TempDir::new` (`build.rs:503-512`): use `create_dir`, which fails
  if the folder exists, and retry with another name, or the `tempfile` crate.
- **F20:** `private_path` (`search_log.rs:33-43`): resolve `..` (with
  `std::path::absolute`) before deciding whether a path is inside the current
  folder.
- **F21:** `check`'s usage errors (`main.rs:1134-1142`) exit 1, the status
  for "it doesn't check". Make them 2, as for `search` and clap.
- **F22:** `members_key` (`lib.rs:3091-3098`) doesn't cover files on disk.
  Low impact: the cache holds one entry, and any edit to the document
  replaces it.
- Pattern, not filed: `Main::answer` holds the `nav` read lock for the whole
  request (`lib.rs:1310`), formatting included, so a long format or a disk
  read delays the checker's next publication. Take the lock only for the
  arms that read `nav`.

## Checked and sound

- **Search pool and staleness (1 Nov §1.4):** bounded workers
  (`search_workers`, default 1; `lib.rs:258-271`). Every job carries the
  version it was computed from, and `searched` answers null unless the
  document is still at that version and the request wasn't cancelled
  (`lib.rs:650-666`). An edit or close supersedes every pending search for
  the document, and a newer request supersedes one of the same kind
  (`lib.rs:993-1019`). `$/cancelRequest` gets `RequestCancelled`.
  `documentChanges` edits name the version when the client supports them
  (`initialize`, `code_actions`, `import_fixes`, the split). Tests:
  `cli/tests/server/lsp.rs:2697-2800`. The one hole is F1, where the range,
  not the version, is stale.
- **One response per request:** `PendingSearch::answer`'s swap
  (`lib.rs:579-583`). Workers, supersession and cancellation all go through
  it.
- **Lock poisoning:** every `Mutex` and `RwLock` is taken with
  `into_inner` on poison, so a panic on one thread doesn't cascade.
- **Diagnostic versions:** edits are applied only between steps, so
  `self.versions` at publication is the version of the text that was checked.
  `answers()` includes only freshly checked steps, so a file whose text
  changed but hasn't been rechecked isn't published under its new version.
- **Semantic tokens:** the marks are sorted (`driver/src/marks.rs:199`), so
  the `u32` deltas can't underflow.
- **Formatting in the editor** never answers with an error. Range formatting
  edits only the declarations that overlap the range, and gives up if the
  declaration count changes.
- **The formatter (§4.1):** refuses any lexical or syntax error. It formats
  each declaration with D1012 brackets, then without them, then copies it
  verbatim (`layout.rs:252-270`). The whole file's tokens, comments and tree
  are checked before anything is returned. Idempotence is tested by the
  fuzzer (`tests/it/fuzz.rs`), the repository sweep and the golden files.
  Its stack and quadratic costs are in the syntax reviews (F5 there).
- **The playground:** a search worker that crashes, or whose search went
  stale, is terminated and replaced, and the request answered
  (`web/lsp-worker.js:69-112`). A crash of the language-server worker
  restarts it (`editor-entry.js:183-219`). Page sessions and server sessions
  use the same limits (`session_for` with `guard + 256 KiB`, so the stack
  guard is the wasm guard), so the library bundle's keys match. Searches in
  the browser get a fresh session each time (no `WARM`), and a stale one is
  ended by terminating its worker, which frees its memory: wasm memory never
  shrinks, so terminating is the right tool.
- **Cancellation in the browser:** the shared-counter hook
  (`watch_edits`) stops a check as soon as the page has sent an edit.
- **`run` and the standalone runtime:** output is flushed at the end, and a
  flush error is a `RunError::Write` (`rt/src/run.rs:96`,
  `driver/src/run.rs:392`). The exit statuses are 0, 1 for an unhandled
  `Fail` and 2 for a runtime error, in both. Standalone ignores `SIGPIPE`
  as Rust's start-up would, checks the manifest version before reading
  anything, and turns a panic into exit 101 after the hook has restored the
  terminal.
- **`run --profile`:** the profile goes to stderr after the run, or from the
  signal thread on Ctrl-C, after the terminal is put back.
- **Host terminal:** signals are blocked before any thread starts and handled
  on a thread of their own. The panic hook uses `try_lock`, so it can't wait
  for itself. Each mode change is saved before it is written, so a failed
  write is still undone.
- **Host stack:** the size arithmetic is checked, the guard is
  `PROT_NONE`, the job and mapping outlive the thread (join, or abort if the
  join fails), and a panic is carried back with `resume_unwind`.
- **Broken pipes:** `exit_quietly_on_broken_pipe` exits 141 only for
  std's print-failure panic.
- **`partial-model`:** used as the oracle in
  `driver/tests/proofs/partial.rs`, so it earns its keep. Its doctests run
  outside nextest, as `docs/testing.md` says.

## The 1 November review's findings in this scope

| Finding | Status |
|---|---|
| §1.4 Background proof actions: no version guard, no bounded pool, no cancellation | **Fixed** (pool, versions, supersession, `$/cancelRequest`, versioned edits, tests). Left: F1 (a stale *range*), SW-1820 (a panic kills the worker; a file's search ignores cancellation) |
| §2 "The search JSON snapshot depends on a wall-clock budget" | **Changed:** the `--at` tests pass `--time 120s` (`cli/tests/server/search.rs:16-20`, SW-1168). It is still a deadline, not a work budget, but one a busy machine doesn't reach |
| §2.x The formatter reparses and checks its output (praise) | Still true; F14, F15 are small gaps in that net |
| §2.x The host stack wrapper documents its assumptions (praise) | Still true; F11 is a consequence of the design it doesn't mention |
| The source fingerprint as a stale-wasm-bundle check | Out of scope here; see `code-review-driver.md` (fixed) |

## Tickets to file

Grouped into lanes; the model as CLAUDE.md suggests.

- **Lane A: language server panic safety** (Sonnet, about 60 min). F2
  (catch per step, rebuild the workspace, `showMessage`, give up after a
  repeat), together with SW-1820 (the search worker), F9 (cancel pending at
  shutdown). Test with a test-only panic hook. Waits for D2730.
- **Lane B: code action ranges from the current text** (Sonnet, about 45
  min). F1: the range from the client's goal diagnostic, a `?` check, and
  the search's chosen position compared; the moved-`?` test.
- **Lane C: project lifecycle in the server** (Sonnet, about 75 min). F7
  (reload on a `stitchwort.yaml` change, a file in a newly listed folder, a
  project created while open; an unreadable project shown as a diagnostic),
  F8 (unload on last close, after D2733), F17, F22.
- **Lane D: CLI fixes** (DeepSeek, about 45 min). F3 (drop sessions in the
  `check`/`audit` loops), F4 (skip hidden folders, don't follow symlinks,
  report unreadable folders, atomic write; after D2731), F19, F20, F21.
- **Lane E: one JSON contract for `--json`** (Sonnet, about 45 min). SW-1692
  plus F5 and F6: always one object, `ok` agreeing with the exit status,
  load failures as `error` plus `diagnostics`; a test per command for a load
  failure. Waits for D2732.
- **Lane F: why steps depend on thread placement** (Opus, about 60-90
  min). F13's investigation: show the dependence on addresses and find the
  structure. If it's an address-keyed cache with reuse, that's a soundness
  ticket of its own.
- **Lane G: bench tidy** (DeepSeek, about 30 min). F12, the misplaced doc
  comment, `--parts` write errors failing the run, `jobs` recorded in the
  baseline and checked, the baseline header corrected.
- **Lane H: small editor and formatter tidy** (DeepSeek, about 45 min). F16,
  F18 (the duplicate options function too), F14, F15, F10 (with SW-1922's
  driver change, or after it), the `nav` lock pattern.
- **F11** (Sonnet, about 30 min, or fold into lane A): ordinary stacks on
  std threads, so that an overflow is reported as one.

## Questions for Matt

- **D2730:** When the language server's checker panics, should the server
  recover (drop that workspace's session, check it again from scratch, show
  a message, stop after a repeat) or exit, so the editor restarts it?
  **[rec: recover; it keeps the other workspaces warm, and exit is the
  fallback if recovery panics too]**
- **D2731:** Should `stitchwort fmt DIR` skip hidden folders (`.git`,
  `.stitchwort`, `.claude`) and not follow symlinked folders? **[rec: yes;
  naming a hidden folder explicitly still formats it]**
- **D2732:** For every `--json` mode (`test`, `search`, `search --at`): always
  exactly one JSON object on stdout, load failures included, with `ok` true
  exactly when the exit status is 0? **[rec: yes; this settles SW-1692]**
- **D2733:** Should the server drop a project's session when its last open
  file closes, trading a cold reopen for memory? **[rec: yes, keeping the
  most recently closed project for a minute]**
