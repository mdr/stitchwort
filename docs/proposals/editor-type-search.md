# Proposal: searching by type from the editor

**Status:** draft 1, 27 November 2026, for Matt's decisions ([§9](#9-decisions-for-matt)).
Ticket SW-4938 (epic proof-search). Related: [search.md](search.md) (the engine), SW-4936
(D3763's variant C layout for `stitchwort search`), SW-4935 (search speed, in progress), SW-4937
(open ability rows in patterns, designed in parallel), [lsp-goal-holes.md](lsp-goal-holes.md) and
[playground-editor.md](playground-editor.md). Code references were read at commit `6f48996ef`.
Labels: **[checked]** read in the source or docs at the place given, or in a source listed at
the end; **[est.]** an estimate, not measured.

## The short answer

**The problem.** Matt asked: "Can I do this sort of search in VS Code or the LSP?" Not today.
The editor has two searches, and neither takes a type: "Search for a proof" at a `?` fills that
one goal (`stitchwort.searchProof`, extension.js `searchForProof`), and Go to Symbol in Workspace
(Cmd+T) finds declarations by name only (`workspace_symbols`, crates/lsp/src/lib.rs:3328)
[checked]. To ask "what in std has type `Nat → List _ → List _`?" you go to a terminal.

**The change.** One new command, **Stitchwort: Search by Type…**, that opens VS Code's
quick-pick box. You type a query in `stitchwort search`'s own syntax (ASCII `->` is fine) and
the list below updates as you type, best match first, each row in D3763's layout:
`filterMap : List a → (a → {e} Option b) → {e} List b`, then the namespace and file on the
right, then the doc's first sentence underneath. Enter puts the name at the cursor and adds
the `import` the file needs; a button on the row goes to the definition instead. The same
command opens pre-filled from a `?` (with its goal) or from a selection (with its type). It
talks to the language server through one new request, `stitchwort/search`, that runs the
engine `stitchwort search` already uses, scoped to the file you're in. The playground gets the
same request behind a small search panel above its editor, like its rename panel.

**What it should do.** A search from the editor answers in what the engine takes once the
library is loaded: about 1.4 s a query today (measured by the orchestrator for SW-4935,
1.7 s warm CLI minus 0.34 s of load and check), so "live" is laggy until SW-4935 lands;
the design keeps the old results on screen and never runs more than one stale search, so it
degrades to "results a second after you stop typing" rather than to a queue. With SW-4935's
target speed (a few hundred ms [est.]) it feels like Cmd+T. Work: about 2.5 hours of agent
time for the server request and the VS Code command, another hour for the playground [est.,
not from measured past lanes].

A coloured **Search view** (a webview with type colouring, like the Goals panel) is the
end-state companion for browsing, and shares its renderer with the playground; I recommend it
as stage 2, after the quick pick has been used ([§4](#4-what-a-result-shows)).

## 1. What exists today

- **The engine** [checked]. `Session::search(text, options, scope)` (crates/driver/src/
  search.rs:572) takes the CLI's query text and returns a `Report` whose results carry the full
  name, kind, type (printed), file and line, the doc's first sentence (`summary`), the `import`
  line that brings the name into scope, and ranking fields (search.rs:476). `Scope` has three
  forms (search.rs:551): a project's namespaces, one file, or a file of a project
  (`ProjectFile`, used by `search --at`), in which "a pattern sees names as the file does". The
  last is what the editor wants: a pattern written in a file means what it would mean there.
- **The server's search machinery** [checked]. Proof searches already run off the checker
  thread, on a pool of search workers (`search_worker`, lib.rs:1435), each keeping a warm
  session with the library loaded and rewinding it after each search (`Warm`,
  `with_project_session`, lib.rs:5270-5330: "loading the library again is most of a search of a
  small project"). A request's `$/cancelRequest` sets its flag; a search **still queued** is
  then skipped, but one **already running** isn't stopped: "the sessions only carry the flag
  ... and nothing turns on the check of it ... so it runs to its end" (lib.rs:1229-1236).
  That matters for searching as you type ([§6](#6-how-it-reaches-the-server)).
- **The client** [checked]. extension.js routes `stitchwort.searchProof` through the
  language client's `executeCommand` middleware, shows a cancellable progress notification,
  then a quick pick of the proofs found. The Goals panel is a webview (`createWebviewPanel`)
  styled with VS Code's theme variables. The import quick fix ("Add `import Std (Map)`") is
  built server-side from a diagnostic's `data.import` (lib.rs:1988).
- **The playground** [checked]. CodeMirror 6 talking to the same language server compiled to
  WebAssembly, in a worker; proof searches run in a second worker (web/lsp-search-worker.js),
  and "a stale search is stopped by terminating this worker" (its line 8), after which the
  replacement reloads the library (17 s in the browser, lib.rs:5289). It has a small pick
  panel above the editor (web/editor/src/editor-entry.js:1062), used for proof picks and rename.

## 2. How other editors do it

All checked on 27 November 2026; sources at the end.

| Tool | How you start it | How results show | What picking does | Live? |
|---|---|---|---|---|
| **Lean 4, vscode-lean4** "Search With Loogle…" (`lean4.loogle.search`) [V1, V2, V3] | command; pre-filled with the editor's selection | a webview panel beside the editor (the Infoview's column): name as a link, ` @ module`, type on the next line; the doc field is fetched but not shown | the name opens the online Mathlib docs in VS Code's Simple Browser; nothing is inserted; "did you mean" suggestions rerun the query | no: Enter or the Find button; queries the Loogle web service, not the local project |
| **Lean 4, LeanSearchClient** `#loogle q`, `#leansearch`, `#search` [V4] | written in the file, as a command, term or tactic | the Infoview, as "Try this" suggestions | clicking replaces the query text in the file (or a code action does) | rechecked as the file is edited |
| **Haskell, haskell-tools.nvim** (Neovim) [V5] | a key on a name: searches Hoogle for the type signature under the cursor, else the word | a Telescope picker (live fuzzy list) | Enter copies `name :: signature`; Ctrl-R replaces the word under the cursor ("hole-driven development"); Ctrl-B opens the Hackage docs | the picker filters as you type; a local `hoogle` is recommended for speed |
| **Haskell, VS Code** | no extension found that searches Hoogle by type from a quick pick; Haskell Spotlight (Alt+H) searches Hoogle, but its listing doesn't say how [V6] | | | |
| **Elm, vscode-elm-signature** [V7] | a "filter signatures" item in a tree view | a tree view of the project's own signatures | not described | filter by name or type signature |
| **rust-analyzer** [V8] | Structural Search Replace (`rust-analyzer.ssr`) takes a rule `pattern ==>> replacement`; workspace symbols take `#` (all symbols) and `*` (dependencies) suffixes | SSR edits code; it is not a search list | | |
| **Agda** "Search About", C-c C-z (Emacs mode, since 2.5.1) [V9] | a prompt for identifiers and string literals | the info buffer | nothing to pick | no |
| **Idris 2** | the LSP offers expression search at a hole as a code action (at most 5 results, 5 s) [V10]; no editor type search found | | | |

What carries over:

- **Insert the name, and say where it came from.** haskell-tools makes replace-the-word a key of
  its own; Loogle in VS Code inserts nothing and its users asked for project-only results
  (Zulip, June 2024 [V2]). We have both for free: the engine searches the project, and gives the
  import line.
- **Pre-fill from the selection** (Loogle does).
- **A webview is clunkier for typing** than a native box: vscode-lean4's maintainer said so of
  LoogleView, and users found its font ignored VS Code's settings [V2]. Hence the quick pick
  first, and a webview only for browsing.
- **Cmd+T can't carry it.** VS Code's workspace-symbol picker fuzzy-matches each symbol's
  *label* (its name) against what you typed and drops what doesn't match
  (symbolsQuickAccess.ts, `scoreFuzzy2(symbolLabel, …)` then `continue`) [V11]. A type query
  wouldn't match any names, so reusing `workspace/symbol` the way rust-analyzer reuses it for
  `#` and `*` would show nothing.

## 3. How a user starts a search

1. **The command palette or a key**: "Stitchwort: Search by Type…" opens the quick pick,
   empty, with the placeholder `a type, a statement, or "name": Nat -> List _ -> List _`.
   Suggested key: none by default (Ctrl+Alt+T and similar clash across platforms); users bind
   it. *(Orchestrator's call: a key can be added later.)*
2. **From a `?`**: a code action "Search by type for this goal" next to "Search for a proof",
   opening the quick pick with `⊢ <goal>` pre-filled (the goal as printed; the query syntax
   already accepts a pasted goal, docs/syntax.md "The query"). Unlike "Search for a proof" it
   doesn't try to close the goal; it lists what has that shape, for you to read and choose.
3. **From a selection**: with text selected in a `.sw` file, the command pre-fills with the
   selection's type when the selection is an expression the server can type (the hover-on-a-
   selection request already computes it, extension.js `provideHover`), else with the selected
   text itself (so a selected type, or a goal copied from the Goals panel, is searched as
   written). Also in the editor's context menu.
4. **From hover** (optional, stage 2): a hover's type gets a "Search for this type" link.
   VS Code shows command links in a language server's hovers only when the client trusts them;
   vscode-languageclient 9 lets the extension trust a named list of commands
   (`markdown.isTrusted: {enabledCommands: […]}`, client.ts:382) [V12], so this can be limited
   to the one search command. It's a small convenience on top of 3.

Not proposed: a search-as-you-type inside the file (`#loogle`-style). Stitchwort has
`stitchwort search` and the `?`; a search statement in source would be a language change.

## 4. What a result shows

D3763 (variant C, SW-4936) is: **short name** (bold) ` : ` *type* (coloured as code), then on
the right the namespace and path (dim), and the doc's first sentence on the next line (green,
italic); "N matches for <query>" above; a tier note only when results are looser than exact.
What each VS Code surface can show [checked in vscode.d.ts, V13]:

| Surface | Name and type | Namespace, path | Doc line | Colour | Typing a query |
|---|---|---|---|---|---|
| **Quick pick** (`createQuickPick`) | `label`, "rendered prominently"; icons by `$(name)` | `description`, "less prominently in the same line" | `detail`, "less prominently in a separate line" | none: theme icons only; no bold, no colours | its own box, native, keyboard-first |
| **Tree view** | `label` (a `TreeItemLabel` can highlight character ranges) | `description` (dim) | only in the hover `tooltip` (Markdown, where a code block is coloured) | highlight ranges only | none: needs a separate input box |
| **Webview** (panel or view) | anything: HTML with VS Code's theme colours, as the Goals panel does | anything | anything | full: the type coloured by token kind, as in the editor | an HTML input: works, but VS Code's own keys (Esc, focus) need wiring, and LoogleView's users found it clunky [V2] |

So variant C maps onto the quick pick almost exactly, without colour:

```
label:        $(symbol-function) filterMap : List a → (a → {e} Option b) → {e} List b
description:  Std.List  std/List/Toolkit.sw:204
detail:       Keeps the `Some` results, in order.
```

- The icon carries the kind (function, theorem, constructor: `symbol-function`,
  `symbol-key`/a theorem icon, `symbol-enum-member`), standing in for the dropped category
  labels; the Stitchwort extension already has a `theorem` semantic token type to match.
- The type in the label is shortened as the CLI shortens it (SW-4936's work: leading
  parameters only later ones use left out). A long type is cut with an ellipsis by VS Code;
  the full type is in the hover of the definition you land on.
- "N matches for …" and the tier note go in the quick pick's `title` and `prompt`; an error in
  the query (it doesn't parse or elaborate yet, which is most of the time while typing) goes in
  `prompt` too, and the previous results stay listed.
- Open theorems get ` (open goal)` after the name, as in the CLI.

**One trap, and how to avoid it.** A quick pick filters and re-sorts its items by fuzzy-matching
what you typed against each label (quickInputList.ts `filter`, `compareEntries`) [V14]. Two
things are needed: every item `alwaysShow: true`, so items whose label doesn't match aren't
hidden; and the server's order must survive. Items whose label happens to fuzzy-match the query
(likely, since the label contains the type you typed) are sorted ahead of the others by match
position. The switch that turns that off, `sortByLabel`, is still a proposed API, with the VS Code
team's own note that "it is a bug that we need this API at all" [V15]; proposed APIs are "only
available in Insiders distribution", behind a launch flag [V16], so the Stitchwort extension
can't use it in the VS Code Matt runs. Mitigations, in order: test whether the type queries
people type actually get reordered (VS Code's fuzzy matcher, `matchesFuzzyIconAware`, may not
match queries with spaces and arrows at all); if they do, put the type in `description` instead
of the label (name prominent, type dim on the same line), which keeps the server's order for any
query that isn't a name. This is the first thing the implementation lane checks.

**The Search view (stage 2).** A webview view in the panel area (beside Problems and Terminal)
showing the last search in full variant C, with the type coloured by the server's token kinds,
the whole doc on expand, and the same actions as buttons. It keeps results while you work (the
quick pick vanishes on the first click elsewhere) and is where "show all 37" goes. Its HTML
renderer is a plain JS module that the playground's panel uses too. I'd build it after the quick
pick has had some use, since the quick pick answers the question Matt asked.

## 5. What picking does, and the keys

| Key | Action |
|---|---|
| typing | the query; results update ([§6](#6-how-it-reaches-the-server)) |
| Up/Down | move through results |
| **Enter** | **insert the name at the cursor** (replacing the selection or a `?` the search started from), and add the `import` the file needs, in one edit (one undo) |
| item button `$(go-to-file)` | go to the definition (std files open read-only, as Go to Definition does today) |
| item button `$(copy)` | copy `name : type` |
| Esc | close; nothing changes |

- **The name inserted** is the shortest the file can use once the import is there
  (`List.filterMap` after `import Std (List)`), which is how the import line already reads
  (`import` in the JSON). For a theorem at a `?`, it's the name alone, not an applied proof:
  "Search for a proof" is the command that builds proofs.
- **The import** is the edit of the existing quick fix ("append to the file's `import` of that
  namespace if it has one, else a new line after the last `import`", docs/syntax.md), computed
  by the server for each result; no edit when the file already has it.
- **Why Enter inserts** rather than goes to the definition: the search exists to find something
  to use in the code you're writing, and inserting with the import saves the step people get
  wrong. Haskell-tools.nvim, the closest comparison, makes replace-the-word a primary key [V5].
  The other choice is reasonable too (Cmd+T's Enter goes to the symbol), so it's
  [D3764](#9-decisions-for-matt).
- When the command was started with no `.sw` editor active (from the palette in a README, say),
  there's nowhere to insert: Enter goes to the definition, and the placeholder says so.

## 6. How it reaches the server

**A custom request, `stitchwort/search`**, rather than `workspace/executeCommand`. Both reach the
same code; a custom request is the honest shape for a query with a typed answer, as
`stitchwort/goalAt`, `stitchwort/contextAt` and `stitchwort/tests` already are, and it needs no
client middleware. (`stitchwort.searchProof` is a command because a code action has to name one.)

```
→ stitchwort/search {textDocument?: {uri}, position?, query: "Nat -> List _ -> List _",
                     limit: 50, rewrite?: false}
← {version: 1, query: {...}, searchTier, total, warnings,
   results: [{...the --json fields...,
              short: "filterMap", namespace: "Std.List",
              location: {uri, range},            // stitchwort-std: or file:, as Go to Definition gives
              insertText: "List.filterMap",
              additionalTextEdits: [TextEdit],   // the import, or []
              typeTokens?: [[start, length, kind]]  // stage 2, for colour
             }]}
  or {version: 1, error: {code, message}}        // a query that doesn't parse or elaborate
```

- **Scope**: with a document, `Scope::ProjectFile` (or `Scope::File` for a file on its own), with
  the editor's unsaved text of the project's open files, as "Search for a proof" reads them
  (D3519). Without one, the workspace's project, as the CLI run in its folder.
- **Where it runs**: on the existing search-worker pool, with the warm session, so the library
  isn't loaded per query. The project's own declarations still have to be brought into the warm
  session each time, as `search --at` does today; if that turns out to be most of the time (to
  measure), the worker keeps the project loaded until a file changes. That is SW-4935
  territory and shared with it.
- **Typing**: the client waits 200 ms after the last keystroke, then sends the query. While a
  search runs, it sends nothing more; when it returns, if the text has moved on, it sends the
  latest text (at most one search running and one waiting, "latest wins"). It also sends
  `$/cancelRequest` for the superseded one, which skips it if it hasn't started. Results of an
  older query are shown only if nothing newer has answered. The quick pick's `busy` spinner is on
  while a search runs.
- **Stopping a running search** is the one engine change worth making: the search loop checks the
  cancel flag between candidates (it already carries the flag; nothing reads it, lib.rs:1233).
  With that, a superseded query costs at most one candidate's comparison, and typing never waits
  for a stale search. Until it's in, "latest wins" above keeps the waste to one search.
- **Latency targets** [est.]: a query that fails to parse answers at once (no search). For
  results, under 300 ms feels live; 1 s is usable with the debounce and the busy indicator; above
  that, live updating is worse than Enter-to-search. Today's engine is about 1.4 s a query
  (SW-4935's measurement), so: build it live, and let SW-4935 bring it under the bar. A setting
  `stitchwort.typeSearch.live` (default true) turns live updating off, searching on Enter instead,
  for slow machines and large projects. *(Orchestrator's call.)*
- **Limit**: 50 results to the quick pick (it scrolls); the CLI's 10 is for a terminal.

## 7. The playground

The same request, the same answer. The playground's server runs searches in its second worker,
where the only way to stop one is to terminate the worker, and the replacement reloads the
library (17 s) [checked, §1]. So the playground never terminates for a superseded type search:
it uses "latest wins" only, with a longer debounce (400 ms [est.]), and searches on Enter if a
query took over 2 s. A WebAssembly search is slower than a native one [est.: 2 to 4×, not
measured for search]; once the cancel check of §6 is in, the worker
can drop a stale search itself instead.

The UI is a search panel above the editor, like the rename panel: a text field and a live list
(arrow keys, Enter inserts, a "Go to" link per row), opened by a toolbar button and Ctrl+K (or
Cmd+K) in the editor *(orchestrator's call: the key)*. Its rows are drawn by the same renderer as
VS Code's stage-2 Search view, so the playground gets colour from the start (it has no quick-pick
limits).

## 8. Options and the recommendation

| | A. Quick pick | B. Search view (webview) only | C. Quick pick now, Search view later |
|---|---|---|---|
| Typing | native, keyboard-first, like Cmd+T | HTML field; focus and keys to wire | native |
| Variant C | all of it but colour and bold | all of it | all of it, in the view |
| Results stay | no (closes on click away) | yes | yes, in the view |
| Shares with the playground | the request | request and renderer | request and renderer |
| Cost [est., agent time] | 2.5 h with the server request | 4 h | 2.5 h, then 2 h |

**Recommendation: C.** The quick pick answers "can I do this search in VS Code" with the least
new surface and the best typing; the Search view is the end state for browsing and colour, and
the playground's panel is that view's renderer from the start. Both sit on one request whose
answer is the CLI's JSON plus what an editor needs (location, insert text, import edit).

## 9. Decisions for Matt

- **D3764: Enter in the search box inserts the name and its import (a button goes to the
  definition)?** [rec: yes]. The alternative is Cmd+T's convention, Enter goes to the
  definition, with insert on a button. Inserting fits the job (finding something to use) and
  saves writing the import.
- **D3765: Build the quick pick now and the coloured Search view after it has been used
  (option C)?** [rec: yes]. The quick pick can't colour the type or show the name in bold
  (VS Code allows only icons there), so in VS Code variant C shows uncoloured until the view
  exists; the playground's panel is coloured from the start.

Orchestrator's calls, recorded here: the command's name ("Stitchwort: Search by Type…"), no
default key, the custom request's name and shape, 200 ms debounce and "latest wins", the
`stitchwort.typeSearch.live` setting, 50 results, the playground's key, and whether the label
or the description carries the type (decided by the test in §4).

## 10. Implementation sketch

Stage 1 (one Sonnet lane, about 2.5 h [est.]):

1. **Server** (crates/lsp/src/lib.rs): a `SearchKind::Types { query, limit, rewrite }` on the
   existing search queue; runs `Session::search` in `with_project_session` with
   `Scope::ProjectFile`/`File`; adds `location`, `short`, `namespace`, `insertText` and the import
   `TextEdit` (reusing the import quick fix's edit builder, lib.rs:1988) to each result. Routed as
   `stitchwort/search` beside `stitchwort/contextAt`.
2. **Engine** (crates/driver/src/search.rs): read the shared cancel flag between candidates
   (and return no report when set). Small, and SW-4935 may touch the same loop: run it after
   SW-4935 or in it.
3. **VS Code** (editors/vscode): `stitchwort.searchByType` in package.json (command palette, editor
   context menu when a `.sw` file has a selection); a `typeSearch.js` with the quick pick, the
   debounce and "latest wins", the item mapping (pure functions in client.js, unit-tested in
   editors/vscode/test like `proofPicks`), Enter applying the insert plus import edit, the two
   item buttons; the `?` code action "Search by type for this goal" from the server, carrying the
   goal text.
4. **Tests**: a server test of `stitchwort/search` on a small project (a result's insert text and
   import edit; a superseded request answered with null); the client's mapping unit tests; first,
   the §4 check of quick-pick ordering, by hand in VS Code by Matt or in the extension test host.
5. **Docs**: docs/syntax.md's search section gets "In the editor" (as `search --at` has), and the
   guide's search page a line and a screenshot-free example.

Stage 1b (playground, about 1 h [est.]): the search panel in web/editor/src/editor-entry.js on
the same request; no worker termination for type searches.

Stage 2 (about 2 h [est.]): `typeTokens` in the answer; the renderer module; the Search view
(`registerWebviewViewProvider`) and the playground panel using it; the hover link (§3, 4).

## Sources

All read on 27 November 2026.

- [V1] vscode-lean4 `package.json`, command `lean4.loogle.search`, "Search With Loogle…":
  https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/package.json
- [V2] Zulip, "LoogleView" (Marc Huisinga, June 2024: the view from 0.0.162, unicode input, clunkier
  input than before, font and width complaints, requests for local and project-only modes):
  https://leanprover-community.github.io/archive/stream/270676-lean4/topic/LoogleView.html
- [V3] vscode-lean4 `src/loogleview.ts` (a `createWebviewPanel` in the Infoview's column, the
  selection as the initial query) and `loogleview/index.ts` (Enter or Find; GET
  `https://loogle.lean-lang.org/json?q=…`; name links to the Mathlib docs in the Simple Browser;
  doc not shown; nothing inserted): https://github.com/leanprover/vscode-lean4/tree/master/vscode-lean4
- [V4] LeanSearchClient README (`#search`, `#leansearch`, `#statesearch`, `#loogle`; "Try this"
  options, "clicking these replaces the query text"):
  https://github.com/leanprover-community/LeanSearchClient
- [V5] haskell-tools.nvim README (`hoogle_signature`; Telescope; `<CR>` copies, `<C-r>` replaces
  the word, `<C-b>` opens Hackage; local hoogle recommended): https://github.com/MrcJkb/haskell-tools.nvim
- [V6] Haskell Spotlight, Marketplace listing and https://github.com/visortelle/hackage-ui
  (searches Hoogle and Hackage, Alt+H; how is not described).
- [V7] vscode-elm-signature README: https://github.com/jlengrand/vscode-elm-signature
- [V8] rust-analyzer manual, Features (Structural Search Replace, `rust-analyzer.ssr`; workspace
  symbol `#` and `*`): https://rust-analyzer.github.io/book/features.html
- [V9] Agda docs, Search About: https://agda.readthedocs.io/en/latest/tools/search-about.html
- [V10] idris2-lsp README (expression search as a code action; time limit 5000 ms, at most 5
  results): https://github.com/idris-community/idris2-lsp
- [V11] VS Code `src/vs/workbench/contrib/search/browser/symbolsQuickAccess.ts`, lines 144-159
  (main branch): https://github.com/microsoft/vscode
- [V12] vscode-languageclient 9.0.1, `client/src/common/client.ts:382`, `markdown.isTrusted`:
  https://github.com/microsoft/vscode-languageserver-node/tree/release/client/9.0.1
- [V13] VS Code API, `src/vscode-dts/vscode.d.ts` (main): `QuickPickItem` (line 1896),
  `QuickPick` (`matchOnDescription`, `matchOnDetail`, `keepScrollPosition`, `busy`,
  `onDidTriggerItemButton`), `TreeItem`, `TreeItemLabel.highlights`, `registerWebviewViewProvider`.
- [V14] VS Code `src/vs/platform/quickinput/browser/quickInputList.ts`, `filter` (items not
  matching hidden unless `alwaysShow`) and `compareEntries` (matches sorted first).
- [V15] VS Code `src/vscode-dts/vscode.proposed.quickPickSortByLabel.d.ts` (issue #73904).
- [V16] VS Code docs, Using Proposed API:
  https://code.visualstudio.com/api/advanced-topics/using-proposed-api
