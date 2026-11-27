# Running tests from the keyboard in VS Code

**Status:** design note, 27 November 2026 (SW-4939, an Opus paper lane).
Nothing is built. The decisions in [§6](#6-decisions-for-matt) are Matt's.
Read against `main` at `4cf487f5b`; VS Code's source at commit
`e6d424c4` of microsoft/vscode (27 Nov 2026). Nothing here was tried in a
running VS Code: it is read from the source on both sides.

Matt, 27 Nov 2026: "it'd be quite nice if there's some keyboard shortcuts
where I could rerun the tests, like rerun the tests that just run after I've
made a change ... It'd be nice if there's an easy way to run all the tests
in a project."

## In plain words

**The problem.** VS Code already has keys for all of this (Cmd+; then a
letter: L reruns the last run, E reruns failed tests, A runs everything).
Our extension plugs into the system those keys use, so they work, but
only on runs started from the Testing panel or the gutter's green
triangles. The "▶ Run test" link above each test bypasses that system: a
run started there isn't a "last run", so Cmd+; L doesn't repeat it, and
its failures aren't "failed tests" for Cmd+; E. That is most likely the
button Matt has been pressing. There is also no way to run the tests of
just the project you're in from the keyboard, and Cmd+; A runs every
project in the window (in this repo that includes all of `aoc/`). Nothing
reruns tests on its own when you save.

**The change.** Three small pieces, all in `editors/vscode/runs.js`:

1. Make "▶ Run test" and "▶ Run tests" in a project file start an
   ordinary Testing run, so Cmd+; L and Cmd+; E repeat what you just ran,
   whichever button you used.
2. Add "Stitchwort: Run Project Tests", the tests of the active file's
   project, on Cmd+; P.
3. Offer VS Code's **continuous run** ("run on save"): turn it on for a
   test, a file or a project, and each save reruns them. The test cache
   does the narrowing: a test whose code didn't change comes back from the
   cache, so a save reruns only what the edit touched.

Then a short "In the editor" part of the guide's testing chapter lists
the keys.

**What it should do.** Edit, save, Cmd+; L: the test you ran last runs
again, from any file, with no mouse. With continuous run on, saving is
enough. How long a continuous rerun of a whole project takes when almost
everything is cached has not been measured; it is one `stitchwort test`
per project (estimated well under a second for a small project, more for
`aoc/`); the implementation lane measures it (§5).

## 1. VS Code's own test commands and keys

All in `src/vs/workbench/contrib/testing/browser/testExplorerActions.ts`
(command ids in `common/constants.ts:63-123`). `KeyMod.CtrlCmd` is Cmd on
macOS, so `KeyChord(CtrlCmd|Semicolon, KeyL)` is **Cmd+; then L**.
VS Code's testing page (code.visualstudio.com/docs/debugtest/testing)
doesn't list these; the source does.

| Command (palette title) | Id | macOS key | Where it applies | Source |
|---|---|---|---|---|
| Rerun Last Run | `testing.reRunLastRun` | Cmd+; L | anywhere | 1536-1552 |
| Rerun Failed Tests | `testing.reRunFailTests` | Cmd+; E | anywhere | 1494-1513 |
| Rerun Failed Tests from Last Run | `testing.reRunFailedFromLastRun` | none | anywhere | 1637-1649 |
| Run All Tests | `testing.runAll` | Cmd+; A | anywhere | 654-669 |
| Run Tests in Current File | `testing.runCurrentFile` | Cmd+; F | editor focused | 1330-1343 |
| Run Test at Cursor | `testing.runAtCursor` | Cmd+; C | editor focused | 1133-1146 |
| Cancel Test Run | `testing.cancelRun` | Cmd+; Cmd+X | while running | 707-716 |
| Show Output | `testing.showMostRecentOutput` | Cmd+; Cmd+O | | 872-881 |
| Peek Output | `testing.openOutputPeek` | Cmd+; Cmd+M | | 1678-1686 |
| Refresh Tests | `testing.refreshTests` | Cmd+; Cmd+R | | 1749-1758 |
| Start / Stop Continuous Run | `testing.startContinuousRun`, `testing.stopContinuousRun` | none | needs a profile with `supportsContinuousRun` | 487-511, 397-411 |
| Turn on/off Continuous Run (one item) | `testing.toggleContinuousRunForTest` | none (an eye icon on the item) | same | 279-310 |
| Run Tests (folder, Explorer's right-click menu) | `testing.runByUri` | none | | 1178-1216 |

The Debug and Coverage variants (Cmd+; Cmd+L and so on) need debug and
coverage profiles, which we don't offer.

What the reruns mean, from the code:

- **Rerun Last Run** repeats the most recent result's request, the same
  test ids and profile (`RunOrDebugLastRun`, 1437-1492). A run an
  extension starts itself counts only if its `TestRunRequest` names a
  profile: VS Code records the targets from the profile
  (`api/common/extHostTesting.ts:1005-1015`;
  `contrib/testing/common/testResultService.ts:139-166`, where no profile
  means an empty target list, so a rerun runs nothing).
- **Rerun Failed Tests** takes every test whose latest result, across all
  runs kept, is failed or errored (`RunOrDebugFailedTests`, 1405-1433).
  "From Last Run" takes only the last run's (1590-1635).
- **Run Test at Cursor** runs the test whose range holds the cursor, or
  failing that the nearest test above it (the comment at 1098-1104).
- **Run Tests in Current File** runs the items whose uri is the file
  (1299-1320).
- **Run All** runs every root item (626-650).

`testing.saveBeforeTest` (default on, `common/configuration.ts:142-146`)
saves dirty editors first.

## 2. What works with our controller today

Read from `editors/vscode/runs.js`.

- **Discovery is already whole-workspace.** At start-up `discoverAll`
  (runs.js:195-215) finds every `.sw` file under a `stitchwort.yaml` with
  `findFiles('**/*.sw')`, asks the server for its tests (or reads the
  text), and lists them, project then file then test. A file watcher and
  edits keep the list current (217-228). So the panel knows every test
  before you open a file; nothing to add here.
- **Run All (Cmd+; A)** reaches every test of every project in the window:
  the roots are our project items, and `plan` splits each project into
  namespace groups, three CLI runs at a time (235-269, 337-346). In the
  Stitchwort repo that is every project, `aoc/` included: heavy, and not
  what "the tests in a project" means.
- **Run Tests in Current File (Cmd+; F)** works in project files: the file
  item's uri is the file (143). Outside a project there are no items
  (D2245), so it says "No tests found in this file".
- **Run Test at Cursor (Cmd+; C)** works, but our test items have a
  zero-width range at the start of the test (176) although the server
  sends the declaration's full range (`crates/lsp/src/lens.rs:36-37`). So
  VS Code always takes its fallback, the nearest test above the cursor:
  right inside a test, wrong in a function below the last test.
- **Rerun Last Run (Cmd+; L) and Rerun Failed (Cmd+; E)** work for runs
  started from the Testing panel or the gutter: our items' ids are stable
  (`file#name`, 169), the handler runs whatever `request.include` names,
  and failures are reported as failed or errored per item (297-311). They
  don't see runs started from the **"▶ Run test" code lenses**: those call
  `runTestsOfFile` (32-78), which runs the CLI itself and shows a message,
  never touching the controller.
- **Run a project** works with the mouse: the project row's run button in
  the panel, or right-click the project folder in the Explorer, "Run
  Tests" (`testing.runByUri`; our project item's uri is the folder, 128).
  No key.
- **Continuous run isn't offered**: the one profile is created without
  `supportsContinuousRun` (352), so VS Code shows no eye icon and Start
  Continuous Run says "No test continuous run-enabled profiles were found"
  (testExplorerActions.ts:437-440).

## 3. How other extensions do it

Each read at its repository's HEAD on 27 Nov 2026 (commits in
[Sources](#sources)).

| Extension | Discovery | Run all, rerun | Watch or continuous | Keys it adds |
|---|---|---|---|---|
| rust-analyzer | the server's `discoverTest` requests, whole workspace, lazily per crate ([R1] 60-72); the panel is off by default, `rust-analyzer.testExplorer: false` [R2] | VS Code's | none: `supportsContinuousRun` passed as `false` [R1] 18-40 | none for tests [R2] |
| Python (ms-python) | the test framework's collection over the workspace; rediscovers on save (`python.testing.autoTestDiscoverOnSaveEnabled`, default true) [P2] | VS Code's | none: three profiles, no continuous flag [P1] 157-178 | none for tests [P2] |
| Jest (vscode-jest) | `jest`'s own test list for the workspace | VS Code's, plus "Jest: Run All Tests" [J2] 404-422 | its own **runMode**, default `"watch"` (jest's watch mode reruns tests related to changed files), or `"on-save"`, `"on-demand"` [J3] 154, 289, 504-511; not VS Code's continuous run [J1] 60-88 | Ctrl+Alt+T, run all tests, in JS/TS editors [J2] 541-547 |
| Vitest (official) | Vitest's API, the project's test files | VS Code's | **VS Code's continuous run**: the run profile passes `supportsContinuousRun: true` [V1] 209-218; `vitest.watchOnStartup` starts it at launch [V1] 173-180, [V2]; a `vitest.toggleContinuousRun` command per item [V1] 383-398 | none [V2] |
| Go (vscode-go) | workspace packages and open files, through document symbols; a `**/*_test.go` watcher [G1] 77-79, 187-219 | VS Code's | no continuous profile [G3] 86-130; separately `go.testOnSave` (default false) runs `go test` for the package on save [G2] | none [G2] |
| Lean 4, Haskell | no Testing API controller: no `createTestController` in either source tree [L1], [H1] | | | |

What they share: none binds rerun keys of its own; all rely on VS Code's
Cmd+; chords, and Jest's one binding is "run all". Run-on-save is the
feature people opt into, done either as VS Code's continuous run (Vitest)
or as the extension's own mode (Jest's runMode, Go's `testOnSave`). The
smart part is the tool's: Jest's and Vitest's watch modes rerun the tests
that depend on what changed. Our test cache does the same job from the
other end: it knows which tests' code didn't change.

## 4. Options

**A. Lenses through the Testing API** (project files). `stitchwort.runTest`
and `runTests` find the item (`file#name`, or the file item) and start a
run with `new vscode.TestRunRequest([item], undefined, runProfile)` passed
to the same `runHandler`. Naming the profile is what makes it a "last
run" (§1). Results then show in the panel, the gutter and the failure
peek, like any other run, and Cmd+; L / Cmd+; E repeat them. The one-line
summary message can stay. Files outside a project keep today's path (no
items there, D2245).

**B. Full ranges for test items.** Use `t.range` end as well as start
(runner.js `fromServerTests` keeps only the start). Cmd+; C then runs
the test the cursor is in. A one-line change, plus the text fallback's
ranges (`discoverTests` would need the declaration's end; it can keep the
start-only range, since VS Code's fallback copes).

**C. "Stitchwort: Run Project Tests".** A command that runs the active
file's project item (`rootOf` the active editor, then `projectItem`), by
the same route as A, so it is also a "last run". Bound to **Cmd+; P**
when a Stitchwort editor is focused (`editorLangId == stitchwort`). No
VS Code chord uses `Semicolon, KeyP` (a GitHub code search of
microsoft/vscode for `KeyCode.Semicolon, KeyCode.KeyP` finds nothing; the
same search for `KeyL` finds testExplorerActions.ts, as a control).
Without a key it is still in the palette and on the Explorer's folder
menu as today.

**D. Continuous run with the cache doing the narrowing.** Create the
profile with `supportsContinuousRun: true`. VS Code then calls
`runHandler` once with `request.continuous === true` and keeps the token
alive until the user stops it; the handler runs once, then on each save of
a `.sw` file in an affected project (debounced, say 300 ms, with any run
in flight cancelled) starts a new `TestRun` for the same request. Which
tests to rerun:

- *D1, simple (recommended):* rerun the whole requested scope, but as one
  `stitchwort test --json` per project rather than the namespace split.
  The cache returns every test whose hash didn't change ("cached", guide
  chapter 9, `docs/guide/09-testing.md:25`), so only the touched tests
  compute. Report the fresh results (`cached: false`) and leave the
  others' state alone, so the panel lights up just what the save changed.
- *D2, precise, later:* ask the CLI first which tests are stale (a new
  `stitchwort test --stale --json`, the cache's own key check without
  running) and start only those. Saves the project load of D1 when
  nothing depends on the edit, and lets the panel spin only the tests
  that will rerun. Only worth it if D1 measures slow on `aoc/`.

The extension's own keys for it: VS Code has none (§1). Option: bind
**Cmd+; W** ("watch") to `testing.startContinuousRun` when
`!testing.isContinuousModeOn` and to `testing.stopContinuousRun` when it is
on (the context key, `common/testingContextKeys.ts:15`; no VS Code chord
uses `Semicolon, KeyW`, same search as above). Per item, the panel's eye
icon.

**E. Document the keys.** A short "In the editor" part of guide chapter 9
(after the `stitchwort test` paragraphs), the editor bullets of chapter 1
(`01-getting-started.md:212-213`) pointing at it, and
`editors/vscode/README.md`. A table like §1's, cut to Cmd+; L, E, A, F, C,
P, W.

**Not recommended:**

- *A key per lens action, or rebinding Cmd+; L to our own "rerun".* A
  duplicates VS Code's command for our tests only, and breaks Cmd+; L for
  other languages in the same window.
- *Retiring the lenses in project files.* The gutter triangles do the same
  job there, but the lenses are the visible, labelled button, and with A
  they become the same run.
- *Testing items for files outside a project.* D2245 chose project tests
  only; the lenses cover loose files. A rerun key there would need it
  reopened; not asked for.

## 5. Recommendation and implementation sketch

Do A, B, C, D1 and E in one Sonnet lane (extension JavaScript, no
language change), with the keys of C and D only if Matt agrees to the
bindings (§6).

| Piece | Files | Agent time (est.) |
|---|---|---|
| A: lenses start a Testing run in project files | `editors/vscode/runs.js` (`runTestsOfFile` asks the controller when `rootOf(uri)` is a project; `register` passes it through) | 15 min |
| B: full ranges | `editors/vscode/runner.js` (`fromServerTests`), `runs.js:176`, `test/runner.test.js` | 5 min |
| C: Run Project Tests, Cmd+; P | `runs.js`, `package.json` (`commands`, `keybindings`) | 10 min |
| D1: continuous run | `runs.js` (`createRunProfile(..., true, undefined, true)`, a loop in `runHandler` for `request.continuous`, a whole-project job for it), `package.json` (Cmd+; W) | 30 min |
| E: guide and README | `docs/guide/09-testing.md`, `docs/guide/01-getting-started.md`, `editors/vscode/README.md` | 10 min |

About 1 to 1.5 hours in all, estimated from similar extension lanes. The
pure parts (which job a continuous save runs, which results are fresh)
belong in `runner.js` with unit tests in `editors/vscode/test/`, as today.
The lane also measures, once, a continuous rerun of `aoc/` with nothing
changed and with one day edited, and reports the times: if the unchanged
case is over about two seconds, D2 becomes a follow-up ticket. Hand
testing in VS Code is Matt's (agents don't start GUI apps), so the brief
ends with a short checklist for him: Cmd+; L after a lens run, Cmd+; E
after a failure, Cmd+; P, continuous run with a save.

## 6. Decisions for Matt

Numbered by the orchestrator when brought.

1. **Should the "▶ Run test" links in project files run through the
   Testing panel** (results in the panel, gutter and failure peek, as the
   green triangles do), so Cmd+; L and Cmd+; E repeat them? Files outside
   a project stay as they are. *Recommendation: yes.* It is the piece that
   makes "rerun what I just ran" work from the button Matt uses.
2. **Should we offer run-on-save** (VS Code's continuous run: off until
   you turn it on, for a test, file or project), rerunning through the
   cache so only tests whose code changed compute? *Recommendation: yes,
   off by default*, as Vitest does; not on at start-up (Vitest's
   `watchOnStartup` is off by default too).
3. **Should the extension add default keys**: Cmd+; P for this project's
   tests and Cmd+; W to start or stop run-on-save, both only in Stitchwort
   editors? *Recommendation: yes.* They sit in VS Code's own Cmd+; family
   and clash with none of its chords. The alternative is commands only,
   with the guide showing how to bind them.

## Sources

VS Code, microsoft/vscode at `e6d424c4bce7a07a1133cc530c4570df8dad3558`,
under `src/vs/workbench/`:

- `contrib/testing/browser/testExplorerActions.ts` (line numbers in §1)
- `contrib/testing/common/constants.ts:63-123` (command ids)
- `contrib/testing/common/configuration.ts:137-146` (`gutterEnabled`,
  `saveBeforeTest`)
- `contrib/testing/common/testingContextKeys.ts:15`
- `contrib/testing/common/testResultService.ts:139-166`
- `api/common/extHostTesting.ts:996-1052`
- `src/vscode-dts/vscode.d.ts:18630-18635` (`supportsContinuousRun`),
  18887-18891 (`TestRunRequest.continuous`), 18754 (`createRunProfile`);
  also in `@types/vscode` 1.80.0, below our engine `^1.82.0`.

Other extensions, at HEAD on 27 Nov 2026:

- [R1] rust-lang/rust-analyzer `efc6ca74`, `editors/code/src/test_explorer.ts`;
  [R2] `editors/code/package.json` (`rust-analyzer.testExplorer`, keybindings).
- [P1] microsoft/vscode-python `280bd57d`,
  `src/client/testing/testController/controller.ts`; [P2] `package.json`.
- [J1] jest-community/vscode-jest `b71edf0b`,
  `src/test-provider/test-provider.ts`; [J2] `package.json`; [J3] `README.md`.
- [V1] vitest-dev/vscode `86bb5e8b`, `packages/extension/src/extension.ts`;
  [V2] `package.json`.
- [G1] golang/vscode-go `3ab28d00`, `extension/src/goTest/explore.ts`;
  [G2] `extension/package.json` (`go.testOnSave`, `go.testExplorer.*`);
  [G3] `extension/src/goTest/run.ts`.
- [L1] leanprover/vscode-lean4 `9ac77ca5` and [H1] haskell/vscode-haskell
  `740e6744`: shallow clones searched for `createTestController`, none
  found.
