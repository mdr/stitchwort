# Proposal: projects in the playground

**Status:** draft 2, 20 October 2026 (SW-133). Design only: nothing is
built. Decisions for Matt are D109 to D116, D118 and D119
([§11](#11-decisions-for-matt)), each with a recommended answer. The goal
is Matt's (D105/D106): make the Advent of Code project (`aoc/`) browsable,
editable and runnable in the **local** playground (`web/serve.sh`).
Shareable links are out of scope. Matt would ultimately like to host the
playground publicly as a static site (no server code), so the design must
work there too ([§10](#10-hosting-as-a-static-site)).

## Changes since draft 1

1. **New §10, hosting as a static site**: what must hold, what in today's
   page would need to change (the per-load cache-busting), download size
   and caching, what gets published (and AoC's request not to publish
   puzzle inputs or text), browser storage on a public origin, keeping
   shareable links possible later, and where to host. New decisions D118
   (where and when to host) and D119 (the example inputs).
2. **Day 4 re-measured** after its speed-up: 4.9 s native, 6.8 s in
   WebAssembly with the real input (was 17.0 s and 23.6 s). Every day now
   fits under the 15 s run limit, so D113's reason changed (its answer
   didn't).
3. Decisions renumbered D109 to D116 (D108 was taken), as merged; the
   decisions table is now §11. The project's size is corrected to about
   160 KB (draft 1 said 100 KB, leaving out the example inputs).

Claims are labelled **checked** (with a `file:line` or a source),
**measured** (by me, numbers in [§7](#7-performance-and-limits)),
**inferred** (reasoned from checked facts) or **unverified**. Code references
are to commit `f58a061` (§10 and the day 4 re-measurement: `1e60e6d`).

## Contents

0. [The short version](#0-the-short-version)
1. [What exists today](#1-what-exists-today)
2. [The WebAssembly API for projects](#2-the-webassembly-api-for-projects)
3. [The page: showing and editing a project](#3-the-page-showing-and-editing-a-project)
4. [Check, Tests, Evaluate, JavaScript and Run on a project](#4-check-tests-evaluate-javascript-and-run-on-a-project)
5. [Bundling](#5-bundling)
6. [Saved edits](#6-saved-edits)
7. [Performance and limits](#7-performance-and-limits)
8. [Browser tests](#8-browser-tests)
9. [Stages](#9-stages)
10. [Hosting as a static site](#10-hosting-as-a-static-site)
11. [Decisions for Matt](#11-decisions-for-matt)
- [Sources](#sources)

## 0. The short version

- **The AoC project goes into the Example dropdown** as a group, "Advent of
  Code 2025", with one entry per day. Choosing "Day 2" opens the one shared
  `aoc` project at `Aoc/Day02/Day02.sw`. The single-file examples work
  exactly as today.
- **Above the editor, a row of file tabs** shows the files the chosen day
  is made of: its program, its proofs, and the shared files they use
  (`Common/Range.sw` …). For day 2 that's six tabs. Other files of the
  project are one click away in an "Other files" list. No tabs appear for
  a single-file example.
- **The compiler gets project versions of its functions**:
  `check_project`, `test_project`, `evaluate_project`, `extract_project`
  and `run_project_streaming`. Each takes the project's files as
  (path, text) pairs plus a *target* (namespaces, or a function's full name
  for Run), and calls the same driver code as the CLI
  (`Session::load_project_sources`), so the CLI and the playground give the
  same answers and the same error text, file paths included.
- **As you type, the chosen day is checked, proofs included.** Measured in
  the WebAssembly build: every day with its proofs checks in 0.18 to
  0.26 s, except day 2 with its proofs, 1.1 s. The whole project checks in
  1.3 s. That's fast enough not to make proofs opt-in. Everything checks
  and every test passes in WebAssembly, under the playground's tight stack
  limit.
- **Run** calls `Aoc.DayNN.main`, with the input box filled from the
  committed example input (`aoc/examples/dayNN.txt`). The private puzzle
  inputs (`aoc/inputs/`) are never bundled; you can paste your own.
- **Edits are saved per file** in the browser's storage, marked on their
  tab, and can be reset to the bundled version, per file or all at once. If
  a rebuild changes a file you had edited, your edit is kept and a banner
  offers the new version.
- **Bundling**: `web/build.sh` copies `aoc/src/**/*.sw` and
  `aoc/examples/*.txt` under `web/pkg/projects/aoc/`, with a small
  `manifest.json` listing the files and the days.
- **Hosting later as a static site** (§10) needs one change to today's
  page: it fetches the compiler afresh on every visit (`?load=<time>`),
  which a public site should replace with a content hash written by the
  build. Everything else already uses relative URLs. Recommended: host
  later, on GitHub Pages, as its own task (D118).

## 1. What exists today

- **The page** (`web/index.html`) has one editor (a textarea with a
  coloured copy underneath, `index.html:366-369`), an Example dropdown
  (`index.html:353-356`) filled from `<script type="text/plain">` blocks,
  and five result tabs: Check, Tests, Evaluate, JavaScript, Run
  (`index.html:374-380`). Checked.
- **The compiler runs in a worker** (`web/playground-worker.js`), one
  request at a time. A request that's superseded, stopped or too slow is
  cancelled by terminating the worker; a fresh one starts quickly because
  the page compiles the WebAssembly module once and hands it over
  (`index.html:616-701`). Checking, testing, evaluating and extracting may
  take 60 s, a run 15 s (`CHECK_SECONDS`, `RUN_SECONDS`,
  `index.html:578-580`). Checked.
- **Storage**: one draft for whatever is in the editor
  (`stitchwort.draft`), the chosen example, the Run input, the chosen tab,
  and the test cache, one `HASH passed|failed` line per test
  (`index.html:592-605`, `1232-1242`). Checked.
- **The WebAssembly API** (`crates/web/src/lib.rs`) takes one `source`
  string per function and answers with JSON. Each loads the source as
  `playground.sw` in a fresh `Session`; `check`, `test` and `extract` share
  the most recent load (`lib.rs:409-429`). Checked.
- **Projects in the driver**: `crates/driver/src/project.rs` already
  separates *reading* a project from *checking* it. `project_sources` reads
  `stitchwort.yaml` and walks the source folders through a small `Files`
  interface, with a disk version and an in-memory one (`MemoryFiles`,
  `project.rs:741-832`). `Session::load_project_sources(project, files,
  target)` takes (path, text) pairs directly and checks the target's
  namespaces and what they use, in canonical order (`project.rs:35-151`).
  The CLI's `run NAME` path is `analyse`, `namespace_of`, `load_analysis`,
  `main_named` (`crates/cli/src/main.rs:402-455`). Checked.
- **Before AoC became a project**, `web/build.sh` copied each day's single
  file to `web/pkg/aoc/` with an `index.json`, and the page added an
  optgroup to the dropdown and filled the Run input from the day's example
  (removed in `32cb955`). Checked. This proposal reuses that shape.
- **The project** (`aoc/`): `stitchwort.yaml` says `sources: [src]`; 15
  files, 2,537 lines; 13 namespaces: `Aoc.Common`, `Aoc.Common.Proofs`,
  `Aoc.Day01` to `Aoc.Day06`, and `Aoc.DayNN.Proofs` for days 1, 2, 3, 5
  and 6. Days 2 and 5 import `Aoc.Common`. Each day has a committed example
  input in `aoc/examples/`; `aoc/inputs/` is in `.gitignore`. Checked.

## 2. The WebAssembly API for projects

### 2.1 Functions

New functions beside today's, which stay as they are for single files:

| Function | Answers | Like the CLI's |
|---|---|---|
| `outline_project(paths, texts)` | the namespaces, each with its files and the namespaces it uses; parse only, nothing is checked | (none) |
| `check_project(paths, texts, targets)` | `{ok, errors, warnings, checked, diagnostics}` | `check NS…` |
| `test_project(paths, texts, targets, known)` | as `test`, each result with its `namespace` | `test NS` |
| `evaluate_project(paths, texts, targets, expr)` | as `evaluate` | (`eval` is file-only today) |
| `extract_project(paths, texts, namespace)` | as `extract` | `build --js NS` |
| `run_project_streaming(paths, texts, name, input, maxOutput, sink)` | as `run_streaming` | `run Aoc.Day02.main` |

- **Files** are two arrays of the same length: paths within the project
  (`src/Aoc/Day02/Day02.sw`) and texts. wasm-bindgen passes a JavaScript
  array of strings as a Rust `Vec<String>`; measured: my prototype used
  exactly this. No JSON parser is needed in the WebAssembly (today's API
  has none either).
- **Targets** are namespace names, comma-separated, or empty for the whole
  project, as `Target::Namespaces` / `Target::Everything`
  (`project.rs:18-21`). For Run, the target is a function's full name, and
  its namespace is found by `namespace_of` (`project.rs:155`), as the CLI
  does.
- **Each call is self-contained**: the page sends every file each time.
  The project is about 160 KB, which costs nothing next to checking
  (inferred). As today, `check_project`, `test_project` and
  `extract_project` share the most recent load, now keyed by the files
  *and* the targets, since the page asks Check then Tests for the same
  thing (`lib.rs:412-416`).

### 2.2 Reusing the driver: with or without `stitchwort.yaml`

Two ways, both through the driver:

- **A. Give the WebAssembly the `.sw` files only**, and call
  `Session::load_project_sources`. The build step decides which files are
  sources.
- **B. Give it `stitchwort.yaml` too**, as an in-memory `Files`, and call
  `Session::load_project` (`project.rs:945`), which reads the config and
  walks the folders, exactly as the CLI does.

Measured: B makes the WebAssembly **35% larger**, 3.55 MB against 2.63 MB
today, because it brings in the YAML parser (`serde_saphyr`). A adds 6%
(2.79 MB). Both check the same in my prototype. The config is never edited
in the playground, so B's extra agreement buys little. **Recommended: A
(D112)**, with the build step refusing to bundle unless
`aoc/stitchwort.yaml` says exactly `sources: [src]`, so a change there
can't silently drift from what the CLI reads.

### 2.3 Errors, with their files

Errors already render with the project's paths, the same text the CLI
prints. Measured, with a syntax error put into `Common/Range.sw` and
`Aoc.Day02` checked:

```
[E-PARSE] Error: expected the end of the declaration, but found `match`
   ╭─[ aoc/src/Aoc/Common/Range.sw:9:3 ]
...
[E-NAMESPACE-FAILED] Error: namespace Aoc.Common has errors, so Aoc.Day02 isn't checked
    ╭─[ aoc/src/Aoc/Day02/Day02.sw:23:8 ]
```

For the page to jump to an error, each answer with errors or warnings also
gets `diagnostics`: one entry per diagnostic, in the same order as the
text, with `severity`, `code`, `file` (path within the project), `line` and
`column` of its primary span. The renderer already finds that span
(`render.rs:13`), so this is a small addition (inferred). Parsing the
rendered text with a regular expression would work too, but would break
whenever the rendering changes.

### 2.4 What `outline_project` is for

The page needs to know which files make up a day, to show their tabs
(§3.2). That's the day's namespaces and every namespace they use, which
only the compiler can work out properly (an `import` may be added while
editing). `outline_project` runs the driver's `analyse` (parsing and
dependency edges, no checking) and returns, per namespace, its files and
the namespaces it uses directly. Its cost is unmeasured; it parses but
doesn't check, so it should be a small part of a check (inferred).

## 3. The page: showing and editing a project

### 3.1 Picking a project

The Example dropdown gets an optgroup, "Advent of Code 2025", with "Day 1"
to "Day 6", as before `32cb955`. All six open the **same** `aoc` project;
the day decides which file opens, which tabs show, what is checked, and
what Run runs. Edits are per project, so an edit to `Common/Range.sw` made
while on day 2 is still there on day 5. (D109.)

### 3.2 Showing the files: options

| Option | What it looks like | For | Against |
|---|---|---|---|
| **1. Tabs for the day's files** | A row of tabs above the editor: `Day02.sw`, `Proofs/Part1.sw`, `Proofs/Part2.sw`, `Proofs/Repeated.sw`, `Common/Range.sw`, `Common/Proofs/Range.sw`, then "Other files ▾" | Shows what this day is made of; few tabs (2 to 6 today); familiar | Tabs are computed, so they can change when an `import` changes |
| 2. File tree in a side panel | Folders matching namespaces, as in VS Code | Shows the whole project; scales to 25 days | Takes width from the editor, which already shares the window with the results; on a phone it needs a drawer; most work |
| 3. One "File" dropdown | A second dropdown beside Example | Least work | Hides which files belong together; switching files takes two clicks |
| 4. One editor, files separated by marker lines | As the Go playground does with its `-- name --` lines (txtar) [G1] | No new UI at all | Line numbers in errors stop matching the editor; the files aren't independent; long scrolling |

**Recommended: option 1 (D110).** The tabs are the files of the day's
namespaces (`Aoc.Day02`, `Aoc.Day02.Proofs`) and of every namespace they
use, from `outline_project`, in this order: the program file first, then
the day's proofs, then shared files, each group by path. A file that
differs from the bundled version shows a dot; a file with errors shows a red mark.
The tab row scrolls sideways inside itself on a phone, so the page never
does. "Other files" lists the rest of the project, by path; choosing one
opens it as an extra tab until another day is chosen.

**Which file opens first:** the day's program, `Aoc/DayNN/DayNN.sw` (D109).

### 3.3 Editing

The one editor stays; switching tabs swaps its text, keeping each file's
caret and scroll position while the page is open. Syntax colouring,
Tab-to-indent and undo work as today, except that undo history doesn't
survive a tab switch (a textarea has one history; inferred from how
textareas work, unverified in detail). Rebuilding the editor on a
proper code-editor component would fix that, but is a separate decision
and not needed here.

## 4. Check, Tests, Evaluate, JavaScript and Run on a project

- **As you type** (after the same 250 ms pause as today), the page checks
  the day's target: `Aoc.DayNN` and `Aoc.DayNN.Proofs` (where it exists),
  and so everything they use. Proofs are included, not opt-in (D111):
  measured at 1.1 s for day 2 and at most 0.26 s for the others (§7). The
  status says what was checked, as in "Day 2 and its proofs checked by the
  kernel".
- **"Check every day"**, a button in the Check tab, checks the whole
  project (1.3 s measured). It's for edits to shared files, which can break
  another day.
- **Check tab errors** are grouped by file, each with a link that opens the
  file's tab and puts the caret at the line. An `E-NAMESPACE-FAILED`
  ("Aoc.Common has errors, so Aoc.Day02 isn't checked") is listed after the
  error that caused it.
- **Tests** runs the tests of the day's target, grouped by namespace as
  `stitchwort test NS` prints them (`main.rs:366-374`), with the same
  browser test cache as today (results are keyed by hash, so they carry
  over between days and between project and single-file use; inferred from
  `lib.rs:69-117`). Day 2's tests take 7.5 to 8.7 s the first time
  (measured), under the 60 s limit, and are cached after.
- **Evaluate**: the expression is evaluated after loading the day's target.
  Measured: full names work (`Aoc.Day02.solvePart1 Aoc.Day02.exampleRanges`
  gives `1227775554`); short names don't (`E-UNKNOWN-NAME`), because
  loading a project leaves no namespace open (`project.rs:141`).
  Evaluating *inside* the open file's namespace, so short names work, needs
  new elaborator support. Recommended: full names now, prefilled as above;
  short names later (D115).
- **JavaScript** extracts the exports of the open file's namespace, as
  `build --js NS` does (`Session::extract_namespace`, `driver.rs:361`). No
  AoC day exports anything today, so it will mostly say "Nothing is
  exported".
- **Run** runs `Aoc.DayNN.main` (the button's tooltip says so), in the
  separate run worker as today. The input box starts with the day's
  example input and is saved per day (§6). The 15 s run limit stays
  (D113).

## 5. Bundling

`web/build.sh` (and the `playground` package in `flake.nix`, which copies
the page's files the same way, `flake.nix:104-112`) gains a step:

```
web/pkg/projects/aoc/manifest.json
web/pkg/projects/aoc/src/Aoc/Common/Range.sw   … every .sw under aoc/src
web/pkg/projects/aoc/examples/day01.txt        … every example input
```

```json
{
  "name": "aoc",
  "title": "Advent of Code 2025",
  "files": ["src/Aoc/Common/Proofs/Range.sw", "src/Aoc/Common/Range.sw", "…"],
  "days": [
    { "title": "Day 1", "open": "src/Aoc/Day01/Day01.sw",
      "namespaces": ["Aoc.Day01", "Aoc.Day01.Proofs"],
      "main": "Aoc.Day01.main", "input": "examples/day01.txt" }
  ]
}
```

- **Days come from the folder layout**: each `src/Aoc/DayNN/DayNN.sw` is a
  day, with `Aoc.DayNN.Proofs` if `src/Aoc/DayNN/Proofs/` exists, and its
  example input if `examples/dayNN.txt` exists. This follows the layout
  rule already in place (folders match namespaces, programs in
  `Aoc.DayNN`, proofs in `Aoc.DayNN.Proofs`). A day without an example
  input gets an empty input box.
- **Never the puzzle inputs**: only `aoc/src` and `aoc/examples` are
  copied, by name; `aoc/inputs/` is not read. A browser test checks that
  `pkg/projects/aoc/inputs/` doesn't exist (§8).
- **The config**: as §2.2, the build step stops with an error unless
  `aoc/stitchwort.yaml` is exactly `sources: [src]`.
- The page fetches the manifest at start; if it's missing (an older
  build), the page works as today without the group, as the old
  `loadAoc` did.
- A Rust test in `crates/web` checks every AoC day the way the page will,
  through the new functions, reading `aoc/` from disk: the targets check,
  the tests pass, and each `main` prints the expected answers for its
  example input. That keeps "the playground can show it" in the normal
  test gate, as `the_playground_examples_check_and_pass_their_tests` does
  for the single-file examples (`lib.rs:846`).

## 6. Saved edits

- **Keys**: one per edited file,
  `stitchwort.project.aoc.file.src/Aoc/Day02/Day02.sw`, holding the text
  and a short hash of the bundled text it was edited from. A file whose
  text is back to the bundled one has its key removed. The Run input is
  saved per day (`stitchwort.project.aoc.input.Aoc.Day02.main`); the
  chosen day and open file are saved too.
- **Reset**: "Reset this file" and "Reset the project" (with a
  confirmation) in a small menu by the tabs.
- **When the bundle changes underneath an edit** (a rebuild after a commit
  changed that file): the edit is kept, and a banner says "Day02.sw has
  changed since you edited it", with "Use the new version" and "Keep mine".
  Choosing "Keep mine" records the new hash, so the banner goes. No merge;
  editing in the repository and in the playground at once is not what this
  is for. (D114.) A saved edit to a file the bundle no longer has is
  dropped, with a note in the banner.
- **Space**: browsers allow about 5 MiB of `localStorage` per origin [M1];
  the whole project is about 160 KB (its `.sw` files and example
  inputs), so even a fully edited project fits.
  Writes are wrapped in `try`, as today's are (`index.html:592-594`).
- **Single-file examples keep today's keys**, unchanged.
- **No new, renamed or deleted files** in this version (D115). A new
  namespace means a new file, which means a new tab, path rules and a
  place in the manifest; it can come later.

## 7. Performance and limits

**How measured.** The native numbers are the release CLI
(`target/release/stitchwort`), wall-clock time including starting the
process, in `aoc/`. The WebAssembly numbers are the release build from
`web/build.sh` with a throwaway prototype of `check_project`,
`test_project`, `evaluate_project` and `run_project` (built on
`load_project` and `load_project_sources`; not committed), called from
Node 22.23.3, which uses V8, the same engine as Chrome. Not measured in a
browser. One run each, on Matt's arm64 Mac, 20 October 2026; the
WebAssembly build has the playground's real limits, including its 128 KiB
stack guard (`crates/web/build.rs:18`).

**Checking** (a namespace and everything it uses):

| Target | Native | WebAssembly |
|---|---|---|
| `Aoc.Common` | 0.10 s | 0.19 s |
| `Aoc.Day01` / `Aoc.Day01.Proofs` | 0.12 / 0.20 s | 0.14 / 0.25 s |
| `Aoc.Day02` / `Aoc.Day02.Proofs` | 0.15 / 0.90 s | 0.20 / 1.14 s |
| `Aoc.Day03` / `Aoc.Day03.Proofs` | 0.15 / 0.23 s | 0.17 / 0.26 s |
| `Aoc.Day04` (no proofs) | 0.10 s | 0.11 s |
| `Aoc.Day05` / `Aoc.Day05.Proofs` | 0.16 / 0.18 s | 0.18 / 0.22 s |
| `Aoc.Day06` / `Aoc.Day06.Proofs` | 0.15 / 0.15 s | 0.17 / 0.18 s |
| the whole project | 1.02 s | 1.28 s |
| a one-line single file | | 0.03 s |

**Tests** (all pass in both): about 0.15 to 0.25 s per target, except day 2:
`Aoc.Day02` 5.7 s native, 7.5 s WebAssembly; `Aoc.Day02.Proofs` 6.7 s
native, 8.7 s WebAssembly.

**Runs**, example input: 0.13 to 0.24 s in WebAssembly, printing the same
answers as the CLI. With Matt's real puzzle inputs (read locally, not
copied anywhere): days 1, 2, 3, 5, 6 take 0.2 to 1.3 s in WebAssembly;
day 4 took 17.0 s native and 23.6 s in WebAssembly in draft 1. **Day 4 was
sped up the same day: re-measured, it takes 4.9 s native and 6.8 s in
WebAssembly**, well under the page's 15 s run limit (re-measured 20
October 2026 at `1e60e6d`, same method; the other days were not re-run).

**Memory**: after checking the whole project and every target in one
instance, the WebAssembly memory had grown to 40 MiB (it never shrinks
while the worker lives). Native peak for checking everything: 86 MB.

**What follows:**

- WebAssembly is 1.1 to 1.4 times native here, so checking proofs as you
  type costs little: no need to make it opt-in (D111).
- Day 2 is the slow one: 1.1 s per pause in typing. Each keystroke during a
  check cancels it by restarting the worker, which is cheap (the module is
  already compiled; starting it took 3 ms in Node). If days get slower, a
  later step is to check the program first, then the proofs, so the
  program's errors show sooner.
- Nothing hit the stack guard, which was my main worry for the proofs.
- The limits stay: 60 s for checking and tests, 15 s for a run. Every day,
  real input included, now fits; the slowest run is day 4 at 6.8 s.
  (D113.)

## 8. Browser tests

New tests in `web/tests/browser.mjs`, each with a fresh tab and empty
storage, as now:

1. **The days are listed**: the dropdown has an "Advent of Code 2025" group
   with a day per manifest entry; choosing day 2 opens `Day02.sw`, with its
   tabs in the order of §3.2.
2. **Each day checks, with its proofs**, and the status says so. (Day 2's
   test is the slow one, about 1 s.)
3. **Run prints the example answers** for each day (`Part 1: 3`, `Part 2:
   6` for day 1, and so on), with the input box prefilled.
4. **Tests** pass, grouped by namespace; a second visit shows them as
   cached.
5. **An error in a shared file**: break `Common/Range.sw` on day 2; the
   Check tab shows the error and the `E-NAMESPACE-FAILED` after it, the
   `Common/Range.sw` tab gets its red mark, and clicking the error opens
   that tab with the caret on the line.
6. **Edits survive a reload**, per file, with the edited mark; "Reset this
   file" restores the bundled text and clears the mark.
7. **The bundle changed**: the test server's override map
   (`browser.mjs`, `overrides`) serves a changed `Day02.sw` after a saved
   edit; the banner shows, and both of its buttons do what they say.
8. **Evaluate** with a full name gives the value.
9. **Single-file examples are unchanged**: no file tabs; the existing tests
   stay as they are.
10. **No puzzle input is served**: `pkg/projects/aoc/inputs/` is a 404,
    and the manifest names no file outside `src/` and `examples/`.
11. **On a phone**, the tab row scrolls inside itself and the page doesn't
    scroll sideways (alongside the existing phone test).

## 9. Stages

1. **The API** (§2): the new functions in `crates/web`, the `diagnostics`
   field, Rust tests including the AoC test of §5.
2. **Bundling** (§5) in `web/build.sh` and `flake.nix`.
3. **The page** (§3, §4): the dropdown group, tabs, project-aware tabs and
   status, error links.
4. **Saved edits** (§6).
5. **Browser tests** (§8), written alongside stages 3 and 4.

## 10. Hosting as a static site

Matt would ultimately like the playground on the public web as a **static
site**: a folder of files served as they are, with no server code. Hosting
is not part of this work; this section makes sure nothing here gets in its
way, and lists what hosting itself would need. It covers the playground
generally, not just projects.

### 10.1 What must hold

- **Every file is static.** The compiler already runs entirely in the
  browser, and the page makes no requests of its own to a server
  (checked: its only requests are the WebAssembly, the bindings, the
  worker script and the font; `index.html:5-7`, `626`, `672`, `711`;
  `playground-worker.js:23`). Projects add only static files: the manifest,
  the `.sw` files and the example inputs (§5). No endpoint is needed.
- **Every URL is relative**, so the site works under a path prefix such as
  `https://mdr.github.io/stitchwort/`. Checked, today's page:

  | Where | URL | Under a prefix? |
  |---|---|---|
  | `index.html:626` | `new URL("pkg/stitchwort_web_bg.wasm…", import.meta.url)` | yes: relative to the page |
  | `index.html:672` | `new URL("playground-worker.js…", import.meta.url)` | yes |
  | `index.html:711` | `import("./pkg/stitchwort_web.js…")` | yes |
  | `playground-worker.js:23` | `import("./pkg/stitchwort_web.js…")` | yes: relative to the worker, which sits next to the page |
  | `index.html:5-7` | Google Fonts, absolute `https://` | yes (a third party; see below) |

  No absolute path (`/pkg/…`) and no `localhost` or `127.0.0.1` appears in
  `index.html`, `playground-worker.js` or `build.sh` (checked by search).
  The local addresses are only in `web/serve.sh`, which is for local use.
  **New fetches for projects must follow the same rule**:
  `new URL("pkg/projects/aoc/manifest.json", import.meta.url)`, and file
  paths from the manifest joined onto the manifest's own URL.
- **The worker is a module worker from the same origin**
  (`index.html:672`), which any static host gives (inferred: the worker
  script is served from the same site as the page).
- **The WebAssembly's content type doesn't matter**: the page downloads the
  bytes and then compiles them (`WebAssembly.compile` on an
  `ArrayBuffer`, `index.html:626-628`), which works whatever type the
  server gives; only streaming compilation needs `application/wasm`
  (inferred from the standard; unverified on every host). GitHub Pages
  does send `application/wasm` (checked with `curl -I` on a `.wasm` file
  on `mdn.github.io`, 20 October 2026).
- **One thing to change: cache-busting.** Each page load adds
  `?load=<current time>` to the compiler's URLs (`index.html:623-628`), so
  that a browser never mixes an old worker with a new bundle. Locally,
  `serve.sh` also turns caching off. On a public site this would make
  every visit download the whole compiler again. §10.2 replaces it.
- **Not published**: `web/serve.sh`, and the stress page
  (`web/stress.html`, `stress-worker.js`) unless wanted. The `playground`
  package in `flake.nix` already copies only `index.html`, the worker and
  `pkg/` (`flake.nix:104-112`).
- **The font** comes from Google Fonts. That's allowed on a static site,
  but each visitor's browser contacts Google. Copying the font files into
  the site would avoid it; optional.

### 10.2 Download size and caching

- **Sizes, measured at `1e60e6d`**: the WebAssembly is 2.63 MB (2.79 MB
  with the project functions, §2.2), 0.96 MB gzipped at level 9; the
  bindings 12 KB; the AoC project about 160 KB before compression.
- **Compression is up to the host.** GitHub Pages gzips HTML (checked with
  `curl -I`, `content-encoding: gzip`); whether it compresses `.wasm` is
  **unverified** (the small `.wasm` file I checked came back uncompressed,
  which may only be because it was 83 bytes). Uncompressed, a first visit
  downloads about 2.8 MB; that's acceptable, but worth checking when
  hosting.
- **Caching by content hash.** The build writes `pkg/version.json` with a
  hash of the compiler's files (the WebAssembly, the bindings and the
  worker script). The page fetches it first with `cache: "no-cache"`
  (always asking the server whether it changed, which costs one small
  request), then uses `?v=<hash>` where today it uses `?load=<time>`. The
  worker already passes its own query on to the bindings
  (`playground-worker.js:23`), so it keeps working unchanged. A browser
  then reuses the compiler until a build changes it, and still never mixes
  versions. GitHub Pages sends `cache-control: max-age=600` (checked with
  `curl -I`), so without the hash a returning visitor could get a
  ten-minute-old file next to a new one.
- **The project files** get the same treatment: the manifest records each
  file's hash, the page fetches each file with `?v=<its hash>`, and the
  manifest itself with `cache: "no-cache"`. The same hash is the "edited
  from" hash of a saved edit (§6), so when a bundled file changes, the
  page both downloads the new one and knows to show the D114 banner.
- Renaming the files themselves by hash (`stitchwort_web_bg.3f9a….wasm`)
  would work too, but wasm-bindgen's generated bindings name the
  WebAssembly file, so it's more to rewrite; the query string is enough.

### 10.3 What is published

- **Published**: the compiler, the page, `aoc/src/**/*.sw` (already public
  in the repository) and `aoc/examples/*.txt`.
- **Never published: `aoc/inputs/`.** Guards, at build time:
  - the build copies only `aoc/src/**/*.sw` and `aoc/examples/*.txt`, by
    those patterns, never the whole `aoc/` folder;
  - the build stops with an error if any path it would bundle contains
    `inputs/`, or if the manifest names a file outside `src/` and
    `examples/`;
  - the Nix build reads only files Git tracks, and `aoc/inputs/` is in
    `.gitignore`, so the published `result-playground` can't contain them
    (inferred from how flakes copy a Git repository; the `playground`
    package should also list its AoC files explicitly, as the removed
    `aocSrc` did before `32cb955`);
  - browser test 10 (§8) checks that `pkg/projects/aoc/inputs/` isn't
    served.
- **AoC's request.** The Advent of Code FAQ says (checked, [A1]): "Advent
  of Code is free to *use*, not free to copy", and "If you're posting a
  code repository somewhere, please don't include parts of Advent of Code
  like the puzzle text or your inputs." The real inputs are covered by the
  guards above.
- **The example inputs are copied from the puzzle text**, so on a strict
  reading of that FAQ they are "parts of Advent of Code". The FAQ doesn't
  single them out. A community FAQ on Reddit suggests using the puzzle's
  sample inputs for tests instead of real inputs [A2] (not an official
  source; unverified as the author's view). They're already public in the
  repository (`aoc/examples/`, and in the code: `def example …` in each
  `DayNN.sw`), so the playground adds no new exposure; but if Matt wants
  to follow the FAQ strictly, the repository is the place to change it,
  not just the playground. Options: keep them (common practice, small
  excerpts); or replace each with a made-up input of the same shape, with
  the expected answers worked out by the program. (D119.)
- The FAQ also asks that a website not "look like Advent of Code or [be
  named] something similar" [A1]. A dropdown group titled "Advent of Code
  2025" in a playground that looks nothing like it is a reference, not a
  look-alike (inferred; Matt's call).

### 10.4 Browser storage on a public origin

- `localStorage` belongs to an **origin** (scheme, host and port). On
  GitHub Pages, every project site of one account shares the origin
  `https://mdr.github.io`, so another of Matt's project sites there could
  read the playground's saved edits (inferred from the same-origin rule;
  harmless here, since nothing secret is stored). A custom domain would
  give the playground an origin of its own.
- Saved edits **survive updates** of the site, since the origin doesn't
  change. That's what the D114 banner is for: after an update changes a
  bundled file the visitor had edited, they keep their edit and are
  offered the new version (§6). The test cache survives too and stays
  correct, because its keys include the compiler's fingerprint
  (multi-file.md §8.2).
- Storage is per browser, per device: nothing is shared between
  visitors, and a browser may clear it. Keys keep their `stitchwort.`
  prefix, so they can't collide with other sites on a shared origin.

### 10.5 Shareable links, later

Out of scope (D105), but nothing here prevents them. The state worth
sharing is small and already plain data: the project name, the chosen day,
the edited files (path to text) and the Run input. A later link could put
that, compressed, in the part of the URL after `#`, which browsers never
send to the server, so it works on a static host. To keep that possible:
keep the saved state as such plain data (§6), and don't make the page
depend on anything that exists only in one browser.

### 10.6 Where to host

- **GitHub Pages** fits: it serves a folder of static files, can be
  published from a GitHub Actions workflow, and the repository is already
  on GitHub (`mdr/stitchwort`). The folder would be the Nix build's
  output, `nix build .#playground` (`result-playground` locally), with the
  projects bundle added (§5). Others (Netlify, Cloudflare Pages) would
  serve the same folder; none needs anything this design doesn't provide.
- **Recommended: later, on GitHub Pages, as its own task (D118)**, after
  the projects work. That task would: switch to content-hash caching
  (§10.2), check `.wasm` compression on the real site, add a workflow
  that builds `.#playground` and publishes it, and decide about the font.
  This is a recommendation, not a commitment.

## 11. Decisions for Matt

| ID | Question | Recommended answer |
|---|---|---|
| D109 | How is the project offered? | An "Advent of Code 2025" group in the Example dropdown, one entry per day, all opening the one `aoc` project at that day's program file |
| D110 | How are a project's files shown? | Tabs for the chosen day's files (its namespaces and what they use), plus an "Other files" list; not a file tree or a single file dropdown (§3.2) |
| D111 | Are proofs checked as you type, or on demand? | As you type: the day's program and proofs together (1.1 s at worst, measured), plus a "Check every day" button for the whole project |
| D112 | Does the WebAssembly read `stitchwort.yaml`? | No: it gets the `.sw` files; the build step refuses anything but `sources: [src]` (saves 0.75 MB of WebAssembly) |
| D113 | Change the 15 s run limit for real puzzle inputs? | No: every day fits with its real input; the slowest, day 4, takes 6.8 s in WebAssembly since its speed-up (measured) |
| D114 | A saved edit when the bundled file changes? | Keep the edit, show a banner offering the new version; no merging |
| D115 | Scope of the first version | No adding, renaming or deleting files; Evaluate takes full names (`Aoc.Day02.solvePart1 …`); short names in the open file's namespace later |
| D116 | Is this designed only for `aoc/`? | Build it for any project listed in the build step, but bundle only `aoc/` for now; the day list is AoC-specific (from the folder layout), other projects would list their `main`s |
| D118 | Where and when to host the playground publicly? | **Agreed (Matt, 20 Oct 2026):** GitHub Pages, as a backlog task, not until Stitchwort is further along (§10.6) |
| D119 | Keep the example inputs (copied from the puzzle text) in the repository and the bundle? | **Decided (Matt, 20 Oct 2026):** keep them, and commit and bundle Matt's real puzzle inputs too; AoC's request doesn't persuade us. Supersedes the 'never published' guards in §5 and §10.3 |

## Sources

- [A1] Advent of Code 2025, "About", FAQ "Can I copy/redistribute part of
  Advent of Code?": https://adventofcode.com/2025/about ("Please don't.
  Advent of Code is free to *use*, not free to copy."; "If you're posting
  a code repository somewhere, please don't include parts of Advent of
  Code like the puzzle text or your inputs."; "If you're making a website,
  please don't make it look like Advent of Code or name it something
  similar."). Checked 20 October 2026.
- [A2] r/adventofcode community wiki, "Puzzle Inputs" (via a mirror):
  https://red.127.pp.ua/r/adventofcode/wiki/faqs/copyright/inputs
  (don't share puzzle inputs publicly; use sample inputs from the puzzle
  statements or made-up cases for tests). Community-written, seen only
  through a search summary; unverified.
- [P1] GitHub Pages response headers, checked with `curl -I` on
  `https://mdn.github.io/webassembly-examples/js-api-examples/simple.wasm`
  (`content-type: application/wasm`, `cache-control: max-age=600`, no
  compression) and `https://mdn.github.io/webassembly-examples/`
  (`content-encoding: gzip`, `cache-control: max-age=600`), 20 October
  2026.

- [G1] Go playground, "support multiple input files in txtar format":
  https://go.googlesource.com/playground/+/a7b4d4c4bb72efd2ec20c9f30d5c1e6f09cee3d2%5E%21/
  (text before the first `-- name --` line is `prog.go`; files are
  relative paths). Checked 20 October 2026.
- [M1] MDN, "Storage quotas and eviction criteria":
  https://developer.mozilla.org/en-US/docs/Web/API/Storage_API/Storage_quotas_and_eviction_criteria
  ("Browsers can store up to 5 MiB of local storage, and 5 MiB of session
  storage per origin"; writes past it throw `QuotaExceededError`). Checked
  20 October 2026.
