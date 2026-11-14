# Evaluation: an editor component for the playground

**Status (5 November 2026): implemented (SW-1378).** Matt decided
(D2415–D2428): CodeMirror 6, colour through the existing tokenizer, the
editor on the shared language server with page glue only where the client
has no UI, no phone check, and `coi-serviceworker` shipped so that
cancellation works on GitHub Pages. The playground's editor is now
`web/editor/src/editor-entry.js` (bundled to `dist/editor.bundle.js`);
§5.2.3 says what the page does and what was measured; §5.2.4 how a
project's first diagnostics came down from tens of seconds (SW-1403). Sections 1–8 are the
evaluation that led there, kept as written.

**Evaluation:** for Matt (SW-1118, D2241, D2263), 3 November 2026.
No commitment to implement: editor-roadmap work waits for the tidy-ups. It
covers roadmap items P2 (editor component) and P3 (inline diagnostics) and
step 5 of
[editor-and-playground-roadmap.md](editor-and-playground-roadmap.md).
Facts about the page are read from the code at `lane/SW-1118` (from `main`
`7e0cc8eb`); sizes were measured here unless marked **unverified**. Package
facts are from the npm registry, 3 November 2026.

## 1. Summary

**Recommendation: yes, move to CodeMirror 6, as a vendored, pre-built ES
module bundle, and do it once the shared driver API (roadmap step 1) exists.**
Do not embed Monaco or VS Code in the playground.

- CodeMirror 6 (CM6) adds about 330 kB minified, **109 kB gzipped**, to a page
  that already downloads about **3.5 MB gzipped** (the WebAssembly is 3.1 MB of
  it). The size is not the objection; the build step is.
- Everything the playground wants from an editor maps onto a CM6 extension
  point, and what `crates/web` returns already has the shape CM6 wants (ranges
  in UTF-16 units; typed expressions; goals with positions).
- A working prototype (section 6) shows the worker's diagnostics as lint
  marks and expression types as hover tooltips, in 130 lines.
- Monaco is about 3.2 MB minified (about 0.85 MB gzipped) before any language
  features, is documented as unsupported on mobile, and is styled as an IDE,
  which fights the tour. The VS Code route needs a WebAssembly language
  server that does not exist yet. Neither gains anything CM6 plus the shared
  driver API does not.

## 2. What the page is today

Read from the code, not assumed:

| Fact | Where |
|---|---|
| One static `index.html` (150 kB, 43 kB gz), a module script of about 2,500 lines, no framework, no bundler, no `node_modules`. The 29 guide chapters are separate `.sw` files in `web/guide/`, fetched on demand. | `web/index.html`, `web/guide/` |
| The "build" is only the Rust side: `web/build.sh` runs `cargo build --target wasm32`, `wasm-bindgen`, `wasm-opt -Oz`, then `bundle-std.sh`, `bundle-projects.sh` and `write-version.sh` into `web/pkg/`. Nix builds the same into `.#playground` (`flake.nix`), which GitHub Pages publishes (`.github/workflows/playground.yml`). `index.html` and `playground-worker.js` are copied verbatim. | `web/build.sh`, `flake.nix` |
| Served by any static server with the right `.wasm` type (`web/serve.sh`, `python3 http.server`). Cache-busting by content hashes in `pkg/version.json`; the page appends `?v=…` to every fetch. | `web/serve.sh`, `web/write-version.sh` |
| Tests: `web/test.sh` serves `web/` and drives headless Chrome over the DevTools protocol (`web/tests/browser.mjs`, about 35 s); `colour.test.mjs` tests the tokenizer in node. | `docs/testing.md` |
| The compiler runs in a worker (`playground-worker.js`, 5 kB): stateless requests (`check`, `index`, `test`, `evaluate`, `extract`, `format`, `run`, `live-*`, project variants), re-sent 250 ms after typing stops; terminating the worker is how a request is cancelled. | `web/playground-worker.js` |
| The editor is a `<textarea>` over a `<pre>` of regex-coloured HTML. About 60 places touch the textarea API (`selectionStart`, `setRangeText`, scroll sync, input events); Tab, undo, hover tooltip, Cmd-click, references and the context menu are hand-written. | `web/index.html` |
| Offline: not offline-capable today. There is no service worker, and the page loads the Recursive font from Google Fonts (it degrades to a fallback font). After the first load the browser cache serves it, so a vendored editor would not change this. | `web/index.html` lines 5-7 |
| Role (D2242): showcase and language tour. The Guide is a second view in the same page. | roadmap section 1 |

### Page weight today (measured, release build, 3 Nov 2026)

| File | Raw | gzip -9 | brotli -q11 |
|---|---:|---:|---:|
| `stitchwort_web_bg.wasm` (after `wasm-opt -Oz`) | 8,201,026 | 3,108,235 | 2,194,723 |
| `std.bundle` | 1,612,381 | 337,941 | 274,917 |
| `stitchwort_web.js` (wasm-bindgen glue) | 31,688 | 6,141 | |
| `index.html` | 150,469 | 42,775 | 36,937 |
| `playground-worker.js` | 5,243 | 1,973 | |
| **Total first load** | **about 10.0 MB** | **about 3.5 MB** | |
| `pkg/projects/` (AoC, roguelike; fetched when chosen) | 3.6 MB on disk | | |

GitHub Pages serves gzip; whether it serves brotli is **unverified**.

CM6 as built for the prototype: 336,122 bytes raw, 109,216 gzip, 94,475 brotli
(section 4). That is 3% of the gzipped first load.

## 3. What the playground needs from an editor

"Now" is what the page has already; "Roadmap" is from
[editor-and-playground-roadmap.md](editor-and-playground-roadmap.md).

| Need | Now | Roadmap | Textarea | CM6 | Monaco |
|---|---|---|---|---|---|
| Inline diagnostics (squiggles, gutter marks) | only in the output tab | P3 | cannot (overlay hacks) | `@codemirror/lint` | markers API |
| Hover (type, doc) | hand-built `#navtip` | item 8, 12 | works, hand-built | `hoverTooltip` | hover provider |
| Go to definition, references | Cmd-click, F12, own menus | | works, hand-built | DOM event handlers plus selection; the page's `goToDefinition` stays | built-in commands |
| Goals panel at the cursor | goals list in output | item 3 | selection events work | `updateListener` on selection; `showPanel` or the existing output pane | |
| Completion | none | items 1, 8; SW-1120 | cannot host a menu | `@codemirror/autocomplete`, async sources | built-in widget |
| Signature help, inlay hints | none | items 8, 9 | cannot | tooltip; widget decorations | built-in |
| Share a snippet by URL | none | P1 | independent of the editor (needs only the text) | same | same |
| Tour pages | Guide view, examples dropdown | P5 | fine | doc replaced by `view.setState` | fine |
| Mobile and touch | native textarea: good | P7 | best | contenteditable, works on iOS and Android; known rough edges (below) | documented as unsupported |
| Accessibility | native textarea | | best | contenteditable with `role="textbox"`; screen readers see the rendered lines | has a screen-reader mode, heavy |
| Theming (light/dark, brand) | CSS variables, `prefers-color-scheme` | | native | themes are CSS-in-JS built from your variables; reuse `--hl-*` | its own theme system, tokens by name |

The textarea cannot host the roadmap's completion menu, signature help, inline
hints or squiggles without growing its own editor, and every one of those is an
extension point in CM6.

## 4. CodeMirror 6

### 4.1 Facts

All MIT (registry `license` field), versions and last-publish dates from the
registry on 3 Nov 2026:

| Package | Version | Published |
|---|---|---|
| `@codemirror/view` | 6.43.15 | 19 Oct 2026 |
| `@codemirror/state` | 6.7.6 | 22 Sep 2026 |
| `@codemirror/commands` | 6.11.1 | |
| `@codemirror/language` | 6.13.1 | |
| `@codemirror/lint` | 6.9.7 | |
| `@codemirror/autocomplete` | 6.20.4 | |
| `@codemirror/search` | 6.7.2 | |
| `@lezer/lr`, `@lezer/highlight` | 1.4.12, 1.2.5 | |

Actively maintained. It is largely one maintainer's project (Marijn
Haverbeke); funding and who else maintains it are **unverified**. It is a
stable 6.x API since 2022, with small breaking changes between minors being
rare (from memory, **unverified**). Everything is a plain ES module with no
dependencies outside the `@codemirror`/`@lezer`/`style-mod`/`crelt`/`w3c-keyname`
family.

### 4.2 Size (esbuild 0.27.2, `--bundle --minify --format=esm --target=es2020`)

Measured by bundling tiny entry files (scratch, not committed):

| Bundle | Raw | gzip -9 |
|---|---:|---:|
| `view` + `state` only (an editor, no keymaps) | 201,326 | 65,122 |
| + `commands` (keymap, history), line numbers | 283,916 | 92,065 |
| + `lint`, lint gutter, `hoverTooltip` | 316,595 | 102,602 |
| **Prototype** (also `language` with a stream tokenizer and highlight style, `autocomplete`, `closeBrackets`, bracket matching, and the page code) | **336,122** | **109,216** |

`@codemirror/search` adds about 25 kB raw (**estimate** from its 138 kB
unpacked size; my attempt to bundle it failed because it was not installed).
A Lezer grammar would add `@lezer/lr` and a generated parser table: a few kB
for a grammar of this size (**unverified**). The roadmap's estimate of
150-300 kB minified was close, and slightly low for a set that includes lint,
autocomplete and language support.

### 4.3 How it would load

The page has no build step for JavaScript. Three options:

1. **Vendor a pre-built bundle (recommended).** One ES module, built from a
   small `web/editor/` entry (like `web/proto/codemirror-entry.js`) with
   esbuild, loaded by `<script type="module">`. No import map, no CDN. For Nix
   (`flake.nix` `playground` copies files verbatim) and CI the bundle must be
   made reproducibly: either commit the minified output (about 330 kB per
   upgrade in git history) or build it in the flake with `buildNpmPackage`
   over a committed `package-lock.json` and `esbuild` (adds an `npmDepsHash`
   to maintain). I prefer building it in the flake and in `web/build.sh`
   (which already is "the build" for everything under `pkg/`), and not
   committing output. `web/build.sh` would need `node` and `esbuild`, which
   `nix develop` can provide.
2. **Import map to a CDN** (`esm.sh`, `jsDelivr`, ...). No build step, but it
   puts a third party in the load path, many small requests (CM6 is dozens of
   modules unbundled), no pinning without hashes (an import map has no
   integrity field for modules, **unverified** for current browsers), and
   breaks the browser tests unless they allow the network. Not recommended
   for a site that is a showcase.
3. **Unbundled ESM files copied from `node_modules`**: the same build
   dependency as option 1 without the tree-shaking benefit. No.

The prototype uses option 1 with the bundle committed, for convenience only.

### 4.4 Mapping onto what `crates/web` returns

- **Lint (squiggles).** `linter(async (view) => Diagnostic[])` with
  `{from, to, severity, message, source, actions}`. The `index` action's
  `diagnostics[]` entries have `severity` (`error`, `warning`, `goal`),
  `code`, `message`, `range` `[startLine, startCharacter, endLine,
  endCharacter]` (0-based lines, UTF-16 columns, `nav.rs`), `labels` and
  `notes`. CM6 documents are UTF-16 offsets too, so the conversion is
  `doc.line(l + 1).from + c`. Goals map to `severity: "info"` (shown in the
  prototype for the `?`). Quick fixes from `search_at` (when exposed) become
  `actions: [{name, apply(view, from, to)}]`, which CM6 renders as buttons in
  the tooltip. **A gap:** `check` (the fast per-keystroke request) returns
  diagnostics with `line`/`column` only, no end; the ranges are only in
  `check_index`, which the page's own comments say "takes about as long as a
  check" because it elaborates again. Either lint calls `index` on each
  change (doubling the work per edit; the prototype does this) or `crates/web`
  adds the range to `check`'s diagnostics (small, and the better answer).
- **Hover.** `hoverTooltip((view, pos) => {pos, end, create})`. The page's
  `targetOf(idx, ref)` and `exprs` handling carry over; the prototype shows an
  expression type for the smallest covering range.
- **Autocomplete.** `autocompletion({override: [async (ctx) => ...]})`
  returns `{from, options: [{label, type, detail, apply}]}`. Until a persistent
  worker session exists (roadmap P4, D2243: approximation first) the source can
  offer the names in the last good index's symbols and scope. The worker's
  stateless request model works (one request per completion with the text),
  and `ctx.aborted` and `ctx.addEventListener("abort")` fit worker
  termination as cancellation.
- **Decorations.** Syntax colour as `Decoration.mark` ranges from a
  `ViewPlugin`, and later semantic colours (constructor, theorem, local) from
  `refs[].kind`. Inlay hints are `Decoration.widget`. Goals-at-cursor is an
  `EditorView.updateListener` watching `update.selectionSet`, feeding the
  existing output pane or a `showPanel` panel.
- **Navigation.** `EditorView.domEventHandlers({mousedown})` for Cmd-click;
  `keymap` for F12 and Esc; `EditorSelection` and `scrollIntoView` for
  `goTo`. Read-only library views are `EditorState.readOnly.of(true)`.
- **Undo, Tab, indent, brackets, selection, find.** Provided; the page's
  hand-written Tab handling and its `insertText`-based undo workaround
  (page lines 3190-3230) disappear.

### 4.5 Language support for Stitchwort

| Option | Cost | Notes |
|---|---|---|
| **Reuse the page's `colour(text, mark)`** in a `ViewPlugin`, producing `Decoration.mark` for the visible ranges | S | The tokenizer is tested (`colour.test.mjs`) and already handles nested interpolated strings. It is whole-text and not incremental, but files are small; colour the viewport plus margin, or the whole document (a few ms). Recommended first. |
| `StreamLanguage` tokenizer (what the prototype uses, a toy) | S-M | Line-by-line with a state object; the interpolation mode stack becomes the state. Gains: indentation and bracket matching hooks, `syntaxTree`-less code folding by indent. Needs the tokenizer ported, and its tests. |
| Lezer grammar | M-L | A real syntax tree: folding, selection expansion, indentation, structural navigation, and a base for sticky-scroll style headers. Needs the grammar (layout, string interpolation, `?`, named arguments) kept in step with the Rust parser, which is a duplicate of the language's definition. Defer unless the syntax tree is wanted for something. |
| Semantic tokens from the worker (kind from `refs`) | S after the index | Layer on top of any of the above as an extra decoration set. |

Recommendation: the first row, then semantic colouring from the index. Not a
Lezer grammar for now; duplicating the grammar is a maintenance cost with no
feature that needs it yet.

### 4.6 Costs and risks

- **Mobile.** CM6 is built on `contenteditable` and has supported touch and
  virtual keyboards since 6.0, but contenteditable editing has historically
  been a source of bugs on iOS/Android (autocorrect, composition,
  selection handles). The textarea is the most robust on mobile. Mitigation:
  keep the textarea path as a documented fallback, or test early on a real
  iOS and an Android device (SW-47 is the Firefox/Safari item). **Unverified
  here:** I tested only desktop Chrome.
- **Accessibility.** The contenteditable element gets `role="textbox"`,
  `aria-multiline`, and `aria-label` from `EditorView.contentAttributes`; a
  screen reader reads the visible lines. The CM6 documentation notes
  accessibility as a design goal; I did not test with a screen reader
  (**unverified**). The Monaco route is no better here.
- **Browser tests.** `browser.mjs` types into and reads the textarea
  (`source.value`, selection); the colouring-alignment tests (highlights
  lining up with a textarea) vanish and the rest need a helper that sets and
  reads the document through the view (`view.dispatch`, `view.state.doc`).
  Real keystroke tests need `Input.dispatchKeyEvent`/`insertText`. M.
- **Style injection.** CM6 inserts `<style>` elements at runtime (`style-mod`).
  The page has no Content-Security-Policy today, so this is fine; a future
  strict CSP would need a `nonce` (supported via `EditorView.cspNonce`).
- **Upgrade and trust.** A new dependency family to keep updated, with a
  lockfile; MIT, no network at runtime if vendored.

### 4.7 Effort

| Step | Size |
|---|---|
| Build: `web/editor/` entry and `package.json`, `esbuild` in `web/build.sh` and `flake.nix`, lockfile, CI | S-M |
| Replace the textarea with `EditorView`: keep the `source`-style façade (`getText`, `setText`, `selection`, `onChange`) so the 60 call sites change in one place | M |
| Colour via `colour()` decorations; theme from the page's CSS variables (light and dark) | S |
| Lint marks from diagnostics (and `crates/web` adding ranges to `check`) | S |
| Port hover, Cmd-click/F12, references menu, library read-only view, goTo | M |
| Update the browser tests | M |
| Completion, signature help, goals panel (these are the roadmap items; the editor makes each cheaper) | per item |

Total for "same features, new editor, plus squiggles": **M-L, about a week**,
as the roadmap says. The risk is in the 60 touch points and the tests, not in
CM6.

## 5. Monaco and VS Code, briefly

### 5.1 Monaco (the editor of VS Code)

- **Size, measured** (`monaco-editor` 0.57.0, MIT, published 24 Sep 2026;
  101 MB unpacked on npm). Bundling `editor.api` with all contributions
  (`editor.all`) failed in my esbuild setup because of the package's `exports`
  map, so the figures are from the prebuilt `min/vs/` files: the core chunk
  `editor-*.js` is 2.47 MB raw (617 kB gzip); `editor.main.css` 391 kB (127 kB
  gzip, including the icon font reference); the editor worker alone, which I
  did bundle, 307 kB (95 kB gzip). **About 3.2 MB raw, 0.85 MB gzipped**,
  roughly eight times CM6, before the language workers (JSON, CSS, HTML,
  TypeScript, avoidable by not importing them) and any language client.
- **Mobile:** the project's README answers "Is the editor supported in mobile
  browsers?" with "No."
- **Style:** it looks like VS Code. Right for an IDE, wrong for a page that is
  also a tour with its own typography, and harder to restyle than CM6.
- **Language support:** Monarch tokenizer (comparable to `StreamLanguage`) or
  TextMate via extra libraries.
- **Gains:** familiar VS Code behaviour, a built-in find/replace, minimap,
  multi-cursor, rich hover and completion widgets, and the larger user base for
  the editing features.

### 5.2 The LSP route (`monaco-languageclient`)

`monaco-languageclient` 11.0.3 (MIT, 15 Oct 2026) connects Monaco to a language
server through `vscode-languageclient`, and now depends on the
`@codingame/monaco-vscode-api` family (`monaco-vscode-api` 38.1.3 is 53 MB
unpacked; versions pinned together, ~30 service-override packages in its
dependency list). This is how you reuse the real extension's features in a
browser. Could our wasm build be the server? Partly:

- `stitchwort lsp` (`crates/cli/src/lsp.rs`) is built on the `lsp_server` crate
  (a stdio connection with threads) and `driver::live` (`LiveProject`,
  `LiveFile`), which read files and use threads. The playground uses neither
  (`crates/web` calls `Session` directly). Whether `driver::live` builds for
  `wasm32-unknown-unknown` is **unverified** (the roadmap lists it as an open
  check). A wasm server would need: a library crate for the server loop
  without stdio, a transport as `postMessage` (the `vscode-languageserver`
  browser reader/writer is the normal one), a persistent session in the
  worker (P4), and virtual files for the std library and projects.
- All of that work also pays for the CM6 route (the shared driver API, a
  persistent session), but the LSP protocol in between adds a JSON-RPC layer
  that the playground, which has direct access to the Rust functions, does not
  need. CM6 can call the same position answers directly. An LSP-in-wasm is
  the better investment only if a *second* browser client, such as a VS Code
  web extension, wants the same server.
- What Monaco gains from the LSP: whatever the server implements (definition,
  hover, references, symbols, formatting, completion for named arguments, code
  actions), with no per-feature glue. What CM6 gains from the shared driver
  API is the same, with glue per feature but no protocol, and much less weight.
  `@codemirror/lsp-client` exists (**unverified**: I did not check its state or
  version) if the LSP route is wanted with CM6 too; it would keep the light
  editor.

#### 5.2.1 Trial: the real server in a worker, with CM6 (SW-1375)

(SW-1378 removed the trial pages, `lsp.html` and `lsp-check.mjs`; the workers
moved to `web/`, and the page is §5.2.3. The text below says what the trial
was.)

`web/proto/lsp.html` runs `stitchwort lsp`'s own code (then `crates/cli/src/lsp.rs`,
included into `crates/web` as `crates/web/src/lsp.rs`; now the `stitchwort-lsp`
crate, §5.2.2) in a worker, and
CodeMirror 6 talks to it through `@codemirror/lsp-client` 6.3.0 (MIT, 17 Sep
2026). `web/proto/lsp-check.mjs` drives it in headless Chrome. Measured on
5 Nov 2026 (M-series Mac, Chrome headless):

- **What it took.** `driver::live` and the rest of the server build for
  `wasm32-unknown-unknown` as they are. The seam is `lsp::Inline`: the same
  `Main` and `Checker`, over `Connection::memory()`, with `receive(message)`
  and `tick()` (one namespace's check, or one queued search) in place of the
  threads; the host does the waiting for typing to pause. On wasm, `Url`'s
  file-path conversions are a small shim, and `stitchwort_core::budget::Instant`
  is `web-time`'s clock (search deadlines panic with `std`'s). The native
  server is unchanged apart from the factoring.
- **Works through the stock client, no glue:** diagnostics as squiggles and
  gutter marks, hover (markdown), go to definition in the file and into the
  library (the page's `displayFile` opens a read-only `stitchwort-std:` view
  from `std_source`; hover works there too), find references, formatting,
  named-argument completion after `(`.
- **Works with page glue:** code actions on `?` (the client has no code
  action UI; 17 lines call `textDocument/codeAction` and apply the edit).
- **Not offered by the server:** signature help, rename.
- **Size:** `stitchwort_web_bg.wasm` 8,746,846 → 10,630,961 bytes (+1.88 MB,
  +22%); gzip 3,308,218 → 4,039,332 (+0.73 MB). Before `wasm-opt`, the largest
  parts of the growth are the YAML parser for `stitchwort.yaml`
  (`granit_parser`, `serde_saphyr`, ~0.49 MB, only for projects),
  monomorphised `core`/`alloc` code (~0.7 MB), driver and elab code the
  playground didn't reach (~0.28 MB), `serde_json` (0.15 MB) and `url`/`idna`
  (0.07 MB). The client adds 30 KB gzip over the CM6 prototype (`marked`).
- **Time to first diagnostics:** 0.8–0.9 s from navigation (server ready
  30 ms after the bindings load; the first check 0.7 s).
- **Typing** (edit, then `client.sync()` at once): small file 0.15–0.21 s;
  AoC 2024 day 21 (226 lines) 2.15 s per edit, every edit. The native server
  on the same files: 0.13 s and 1.46 s. Most of the AoC time is the
  checker's own (a file on its own is checked again whole), not wasm (1.5×).
  With the client's own 500 ms pause before syncing, add 0.5 s.
- **Code action** on `n + 0 = n := ?`: 13 s in the worker, and the worker
  is blocked for all of it: no diagnostics meanwhile.

What is left, by size:

1. **Cancellation** (medium). A namespace's check can't be stopped by an
   edit: there is no other thread to set the flag. On the AoC day an edit
   waits up to 2 s behind a stale check. Options: a `SharedArrayBuffer`
   flag (needs cross-origin isolation, which GitHub Pages can't set without
   a service-worker shim), or a check that yields.
2. **Searches block the checker** (small to medium). A second worker for
   searches and `contextAt`, as natively they have threads of their own.
3. **Projects** (medium). The server reads projects from disk
   (`DiskFiles`, `find_project`); the playground has them in memory
   (`crates/web/src/project.rs`). It needs an in-memory `Files` behind the
   same seam.
4. **Packaging** (small). The trial includes the file by `#[path]`; the
   real thing is a `stitchwort-lsp` library crate that the CLI and
   `crates/web` both use, and the playground's own worker and session.
5. **Size** (small, optional): the YAML parser could stay out of a build
   that gets projects pre-parsed.

#### 5.2.2 The language server as the playground's backend (SW-1384)

D2423 (Matt): the playground's editor is built on the shared language
server, with small page glue only where the client has no UI. SW-1384 did
the five items above. Measured on 5 Nov 2026 with `lsp-check.mjs` (headless
Chrome, M-series Mac under other lanes' load, so the times are a little
higher than §5.2.1's).

- **Packaging.** The server is the library crate `crates/lsp`
  (`stitchwort-lsp`): `stitchwort lsp` and `crates/web` both use it, the CLI
  re-exporting it as `stitchwort_cli::lsp` for its tests.
- **Projects from memory.** Every read of a file the editor hasn't opened
  goes through a `Source`: `Disk` natively, `Memory` in the playground,
  whose worker adds the bundled projects (`LanguageServer::add_project`,
  from `pkg/projects/NAME/manifest.json`) at `/playground/NAME`. Their source
  folders come known (`sources: [src]`, D112), and `Files::config` lets such
  files skip parsing `stitchwort.yaml`, so the web build no longer links the
  YAML parser: `stitchwort_web.wasm` 15,100,900 → 14,298,424 bytes before
  `wasm-opt`, `stitchwort_web_bg.wasm` 10,653,029 → 10,016,341 (gzip
  4,047,298 → 3,804,354). With the search worker's code below it is
  10,065,467.
  `lsp.html?project=aoc&open=src/Aoc/Year2024/Day21/Day21.sw` opens that file
  as part of the project: an edit's diagnostics in 0.31 s (median; 2.2 s
  for the same file on its own, which is checked again whole). The **first**
  diagnostics take 26–28 s, almost all in one tick: the project's session
  loads every library file before its first mark (`LiveProject::new`, so
  that rewinding never unloads one), and in the browser there is no check
  cache to load them from. Natively the same happens without a cache (the
  memory test takes 20 s). That is the next thing to fix for projects
  (a bundled check cache for the library, or loading it lazily in the
  browser).
- **Searches off the checker.** A queued search is data (`Search`), not a
  closure. The checker's worker hands each out (`Inline::take_searches`) to
  a second worker (`lsp-search-worker.js`, a `SearchWorker` instantiated
  from the module the first compiled, with the same library and projects)
  and hands the result back (`Inline::searched`), which answers the request
  as the native pool does (null if the document has moved on). A search the
  server answers itself meanwhile (an edit, a newer request,
  `$/cancelRequest`) is dropped from the queue, or, running, stopped by
  terminating that worker, which the next search replaces. During the
  14–16 s search for `n + 0 = n`, hover answers in under 50 ms and an
  edit's diagnostics arrive in 0.38–0.42 s (before: both waited for the
  search, 13 s or more). The search itself takes as long as before.
- **Cancellation.** Two ways were weighed:
  - *A check that yields part-way.* Today the unit of a tick is a
    namespace (a file on its own: the whole file). Yielding inside one
    means turning the elaborator's loop over a namespace's components
    (`elaborate_namespace_untimed`) into a state machine kept across
    ticks: its items borrow the parsed files, the cached path
    (`elaborate_namespace_cached`) and the session's mark and rewind wrap
    it, and `LiveProject::step` and `LiveFile::step` would split to match.
    It works on any host, but it is a large change in the elaborator's core
    loop, and one long declaration still blocks.
  - *A flag in shared memory* (chosen). The page bumps a counter in a
    `SharedArrayBuffer` for each `didOpen`, `didChange` and `didClose`
    (opening another document stops the check of the one before it); the
    worker counts those it has read; `Budget` reads a hook the host installs
    (`Budget::set_cancel_hook`, consulted with the native flag, every
    `POLL` steps) and the worker's hook says whether the page is ahead.
    The check stops as natively, rewinds, and the next tick checks the new
    text. About 60 lines (the hook in `stitchwort-core`, a wasm import, and
    the counter in the page's transport and the worker). It needs
    cross-origin isolation (`COOP: same-origin`, `COEP: require-corp`)
    for `SharedArrayBuffer`; without it the page doesn't create the counter
    and a check runs to its end, as before. Measured on the AoC day on its
    own (a 2.2 s check), a second edit 0.5 s after the first: its
    diagnostics in 2.1–2.2 s with isolation, 3.75–3.8 s without.
  It is the simpler of the two by far, and it works on GitHub Pages only
  through a service worker that adds the two headers to every response
  (`coi-serviceworker`, MIT): the first visit loads the page twice, nothing
  cross-origin may be loaded without CORP (the playground loads nothing
  cross-origin), and where service workers are off (some private browsing
  modes) the page falls back to no cancellation. Whether to ship that shim
  is a decision for Matt; until then cancellation works wherever the host
  sends the headers (`lsp-check.mjs` does).
- **Not done here:** the page itself (`index.html`'s textarea is unchanged;
  the workers are still `web/proto/lsp-worker.js` and
  `lsp-search-worker.js`, which the flake's playground doesn't copy yet),
  and the first-diagnostics cost of projects above. The page is §5.2.3.

#### 5.2.3 The page on CodeMirror and the language server (SW-1378)

What the page does now, with the decisions of D2415–D2428:

- **The editor** is `Editor` in `web/editor/src/editor-entry.js`, which the
  page makes with `createEditor(parent, options)` and uses like the textarea
  it replaced (`value`, `selectionStart`, `setSelectionRange`, `focus`;
  `open` shows a document). It starts the language server's worker
  (`web/lsp-worker.js`, with `lsp-search-worker.js` for proof searches; both
  moved out of `web/proto/`, and the flake's `playground` copies them) and
  connects `@codemirror/lsp-client` to it.
- **Colour** comes from the page's own tokenizer, `colour()`, unchanged: a
  state field marks each stretch it reports with a `hl-KIND` class that the
  page's CSS colours as before (the guide's code uses the same classes and
  variables). Light and dark themes are the page's variables.
- **From the server, through the stock client:** errors underlined (lint
  marks, with a gutter marker) and their messages on hover; hover tooltips
  (the declaration and its whole documentation: the server does not shorten
  it to a first sentence as the page's own tooltip did, D2147); go to
  definition (F12 or Cmd/Ctrl-click) in the file, into the library as a
  read-only document with a bar and a way back (Esc, Cmd+[, the Back button),
  and into other files of a project, which the page opens as a tab; find
  references (Shift+F12, the client's panel); formatting (Shift+Alt+F and the
  Format button: the server leaves a file with a syntax error alone, so the
  page's "Not formatted" panel is gone); completion (the server offers
  named arguments after `(`).
- **Page glue, where the client has no UI:** code actions on a `?`
  (Cmd/Ctrl+. applies the first action's edit; the title shows in the notice
  line meanwhile), and the way back from a jump.
- **Files of a project** are the server's documents at
  `file:///playground/NAME/PATH`: the page hands it each project once
  (`add_project`, with the saved edits applied), and every file shown stays
  open on the server (one `EditorView` each, the others hidden), so the
  project's session stays alive and a tab's edits and undo history are kept
  while it is out of sight. The page's own Tests, Evaluate, JavaScript and Run
  go through `playground-worker.js`; its Check pane shows the server's
  diagnostics (§5.2.5).
- **Cancellation:** the page ships `web/coi-serviceworker.js` (MIT, vendored
  unchanged with its licence header), so on GitHub Pages the page is
  cross-origin isolated after its first visit and the editor creates the
  shared counter (`stats.isolated`). Without isolation (service workers off)
  a check runs to its end as before.
- **A crash** of the server's worker (a trap, or V8's stack running out)
  makes the editor start a new worker, give it the projects and reopen the
  documents (at most three times).
- **Dropped with the textarea:** the page's own index, tooltip, references
  panel and right-click menu (`check_index` and the `index` action of
  `crates/web` were left unused here, and are gone in §5.2.5), the selection-type pill, the
  underline of a name while Cmd is held (the pointer changes instead), and
  the "Not formatted" panel.

Measured on 5 November 2026 (M-series Mac, headless Chrome, the machine at a
load average of 20–90 from other lanes, so the times are rough):

- **Sizes:** `dist/editor.bundle.js` 427,798 bytes (138,130 gzipped; the
  evaluation's estimate was 109 kB gzipped for CodeMirror alone, the client
  and `marked` come on top); `stitchwort_web_bg.wasm` 10,065,473 (3,822,516
  gzipped), the same as §5.2.2's; `index.html` 114,616 bytes (151,488 before:
  the page's own navigation code is gone); the workers 6.4 kB and 1.2 kB, the
  service worker 6 kB.
- **First diagnostics** of a program on its own: 0.6 s after the editor
  starts (the server ready in 25–80 ms); an edit's underline 1.5 s after a
  paste (0.5 s of that is the client's pause before syncing). In an AoC day
  27–40 s (the project is loaded whole before its first marks, as in §5.2.2:
  the next thing to fix); then an edit of the day's file in 0.3 s.
- **A stack overflow in the worker** (SW-1378, SW-1430), now fixed and
  confirmed in headless Chrome. Opening a file of `Aoc.Common` in the editor
  (a jump to it) and then editing the day made V8's stack overflow inside
  the server (a `RangeError` out of `tick`; the instance is unusable
  afterwards, so the editor restarts the server and the project loads
  again). The cause: a navigable session prints the types it noted for
  hover (`flush_navigation`) after a declaration's operation has ended,
  where the budget had no stack floor and no step limit. The background
  check of the rest of the project reaches `Aoc.Year2021.Day11.Proofs`
  (`Parts.sw`) a few seconds after the day's first marks, and there the
  printer recursed without limit, which is why the overflow seemed tied to
  the jump and the edit. Each noted type is now printed within the
  session's limits (`…` where it can't be). Halving the server's guard
  (SW-1378) had only moved the overflow, and gave `Parts.sw` a false
  "ran out of resources"; the server now has the playground sessions' full
  guard again (256 KiB, `crates/web/src/lsp.rs`). Measured with the full
  guard: `Parts.sw` checks clean in Node (85 s for its namespaces, then an
  error edit in 4.1 s); in Chrome the whole AoC project's background check
  finishes 108–118 s after the jump without a crash, and an error edit
  after it is underlined in 1.3 s. Without the printing fix the same
  browser test fails at once with the `RangeError`. The browser test (the
  jump, then the whole project's check, then the error edit) is in
  `web/tests/browser.mjs`; it takes about 140 s, most of it the project's
  check. The editor reports in `stats.idle` when the server's background
  work is done.
- **Lint marks are drawn only near the viewport.** CodeMirror draws only
  the lines in and near its viewport, so a test that looks for an
  underline (`.cm-lintRange-error`) must scroll to it first: a first
  version of the test above timed out without the underline although the
  server had published the error in 0.9 s, because the way back from the
  jump had restored the scrolling to the top of the file.

#### 5.2.4 A project's first diagnostics: the library's check cache (SW-1403)

D2439 (Matt): speed first. A project's first diagnostics took 26–40 s in
Chrome and 40–195 s in Node, because each visit checked the whole standard
library again: `LiveProject::new` loads every library file before its first
mark, and the browser had no check cache.

**Where the time went** (measured 5 November 2026, machine load 30–60):

- Natively, with the worker's limits and no cache, the first diagnostics
  of `Aoc.Year2024.Day21` took 49–106 s, all in one tick: the library
  files 103 s of 106 s (`STITCHWORT_TIMINGS`), the day itself 50 ms.
  `std/Float/Theory.sw` alone was 33–97 s of it.
- With a check cache the same took 1.3 s natively (the library replayed:
  0.3 s of elaboration, 0.2 s in the kernel).
- In Node, on the built WebAssembly, without a cache: 37.8–39.7 s.

**The design: the library's check cache, shipped with the page.** Lazy
loading would have helped less: the AoC days use most of the library, and
`LiveProject` loads it whole up front so that rewinding never unloads a
file (re-checking a namespace would load its files again). Replaying it is
both: as eager as before, and cheap.

- `web/build.sh` (and the flake's `playground`) runs
  `web/bundle-std-cache.mjs` after the WebAssembly and `std.bundle` are
  written. It runs that WebAssembly in Node: `build_library_cache` makes a
  session exactly as the language server makes a project's
  (`stitchwort_lsp::library_bundle`, through the one `session_for`), checks
  the library into a recording store, and writes `pkg/std.cache.gz`
  (gzipped by the script; `LibraryBundle`, `crates/driver/src/check_cache.rs`): an entry per
  library file, as a cache directory holds them, and the files that didn't
  check under the worker's limits (`left_out`, none in WebAssembly). It then
  loads the library back from the bundle and fails the build unless every
  file that can be cached was replayed (67 of 68; `Float/Float.sw` binds
  primitives and is always checked, in 70 ms). About 40 s.
- **Staying in step.** The cache is made by the same WebAssembly that reads
  it, from the same `std.bundle`. Every entry is found by its key, which
  covers the compiler build (version and source fingerprint, which includes
  the target), the entry format, the modes and limits, and the file's text
  and its dependencies' keys. A bundle from another build is not read at
  all (`LibraryBundle::decode` compares the compiler first), and a session
  made differently finds only misses: the library is then checked as
  before, never answered from a mismatched entry. `version.json`'s hash
  covers `std.cache.gz`, so a browser never mixes one build's cache with
  another's WebAssembly.
- **Trust.** Entries are admitted without the kernel's checks, as a cache
  directory's are (check-cache.md, D1660). The per-directory salt, which
  stops a directory reading entries it didn't write, doesn't apply: the
  bundle comes from the build that made the WebAssembly reading it, so
  trusting it is trusting the WebAssembly. Its salt is a constant, so one
  build makes the same bytes each time.
- **In the worker** (`web/lsp-worker.js`), the server starts at once and
  `std.cache.gz` is fetched meanwhile and decompressed with
  `DecompressionStream` (`LanguageServer::load_library_cache`,
  `Options::library`, a cell read when a project or a file on its own is
  loaded). A program on its own doesn't wait for it; a project does
  (`{project}` waits for the fetch). Without it (a 404, another build's)
  `stats.libraryCache` is false and the library is checked as before.
- `LiveProject::new_except` leaves the bundle's `left_out` files, and those
  that need them, to load when a namespace needs them, so a file that can't
  check under the worker's limits doesn't spend the first check failing.
  In WebAssembly none is left out. Natively, with the worker's 512 KiB of
  limits, `Float.Theory.roundMagnitudeSpec` runs out of depth (in
  `Float.Model.bitLengthWhen`). Both builds measure the same thing, bytes
  of stack below where the operation started (`Limits::stack`), but a
  recursion level costs different bytes: WebAssembly keeps only
  address-taken locals in its linear-memory stack, a native frame holds
  every spill, and a debug frame is several times larger again (SW-962).
  Measured natively (SW-1456; `library_bundle`, release build): a
  `Options::new` of 512 KiB (256 KiB usable, the worker's) leaves out
  only `Float/Theory.sw`; 640 KiB (384 KiB usable) leaves out nothing. In a
  debug build, 2 MiB still leaves out 28 files. So no byte limit is
  equivalent to WebAssembly's across builds; a native session that must
  check what the playground checks needs about 1.5 times the guard in a
  release build, and a depth count (`Limits::frames`) instead of bytes is
  what would make them agree.

**Measured after** (same day, load 30–45):

| | before | after |
|---|---|---|
| Node, `Day21` first diagnostics | 37.8–39.7 s | 2.0 s |
| Node, `Year2025/Day02` | — | 2.0 s |
| Chrome, longest server tick on opening day 2 | 25.1 s | 1.2 s |
| Chrome, opening day 2 to its first marks | 25.7 s | 8.8–9.3 s |
| Diagnostics of a day with two errors (Node) | same two messages | same two messages |

The browser's 8.8 s is now mostly the page's own Check of the day
(`playground-worker.js`, whose sessions still check the library), which
the browser test waits for before it looks for marks: the server's part is
a 0.6 s fetch of the cache and ticks of at most 1.2 s.

**Size (SW-1455):** `std.cache` was 14,428,877 bytes; 7,532,898 gzipped,
5,188,475 with brotli. That was more than the WebAssembly: the entries are
for a navigable session with expression types (`+nav+ty`), so they carry what
hover and go to definition need inside library files. Where the bytes went:
the checked terms 9.4 MB (`App` nodes 4.0 MB, `Loc` nodes 2.0 MB), code
navigation 3.1 MB (expression types 0.9, locals and binders 1.1, references
0.7, local types 0.4), the string tables and file names 1.4 MB, the
declarations' index with their content hashes 0.25 MB, and each entry's
header (key, dependency hashes, checksum) 0.24 MB. Two changes to the entry
format (27) make most of it repeat, which compresses well: a node's children
are written as how far back they are rather than by node number (they sit
just before it), and spans in a list in source order as steps from the
previous start (every `Loc` node, and navigation's lists). Together:
10.55 MB raw, 2.49 MB gzipped, 1.86 MB with brotli. The build also
gzips the file itself (`std.cache.gz`): GitHub Pages compresses the file
types it knows, and a `.cache` isn't one, so it would have been sent as it
is. Brotli would save another 0.6 MB, but `DecompressionStream` does not
reliably take it in browsers, and a decoder in the WebAssembly is a new
dependency.

**Next:**

- The page's own Check, Tests, Evaluate and Run (`playground-worker.js`,
  `crates/web/src/lib.rs`) check the library too: the same kind of bundle,
  for its sessions' modes (no navigation, so much smaller entries), would
  cut opening a day to about the server's 2 s.
- The proof searches' worker (`Searcher`) loads the library in its own
  sessions without a cache.
- Smaller still: navigation data (a third of the compressed bytes) is only
  read when a library file is opened, so it could be a second file fetched
  then; the hashes and dependency lists (about 0.3 MB, incompressible) and
  strings repeated between entries are what is left in the rest.

#### 5.2.5 One checker: the Check pane shows the server's diagnostics (SW-1432, SW-1454)

The page checked everything twice: the editor's marks came from the language
server (`lsp-worker.js`, fast since §5.2.4), and the Check pane from
`playground-worker.js`, whose sessions checked the library again (9.5 s for
`Aoc.Year2025.Day02` in Node, most of the 8.8 s the browser took to open a
day). Now there is one checker for diagnostics.

- **The Check pane is the server's.** `serverCheck()` in `web/index.html`
  waits until the server has checked the text on show, then shapes the
  diagnostics it published (errors, warnings, open goals; the same ones the
  editor underlines) as the compiler's check answers were shaped, so the
  rest of the page (the status line, the red file tabs, the error links,
  "Fix the errors first" on the other tabs) is as before. The messages are
  the server's (`[CODE] message`, with the first label's explanation and the
  notes), not the CLI's rendering with a source excerpt. The page's own
  `check` action stays only as the stand-in where there is no language
  server (a host that blocks workers, or a server that crashed for good).
- **Two messages that are not LSP.** `stitchwort/focus` (client to server,
  `{"uris": [...]}`): the files whose namespaces the client wants checked
  with the one being edited, before the rest of the project, and published as
  each is (`LiveProject::set_also`). The page sends the day's own files (its
  program, tests and proofs). Without it the day's proofs, which nothing in
  the day's program uses, were checked after every other namespace of the
  project: two minutes in Chrome. `stitchwort/checked` (server to client,
  `{"versions": {uri: version}}`): once everything the client is looking at
  (the file edited, those it asked for) is checked and published, the
  version of each open document that was checked. The page's
  `Editor.settled(uri)` resolves when its document's current version is
  announced, so a pane never shows the answer for older text, and never
  waits for the rest of the project.
- **Tests, Evaluate, JavaScript and Run (`playground-worker.js`) replay
  the library too.** Its sessions are made as the server's
  (`stitchwort_lsp::library_session`: the same modes and limits, so the same
  cache keys) and read `std.cache` (`load_library_cache`). They check the
  program again before running it; with the cache that costs the program,
  not the library. The tests of a day need a checked session of their own
  (they run in it), so this is a second check of the day's namespaces, in a
  worker beside the server; it is no longer on the way to the Check pane's
  answer.
- **Removed:** `check_index` and `check_index_project` (and their tests),
  the `index` action of `playground-worker.js` and of the in-page
  compiler.
- **Not done:** the proof-search worker (`lsp-search-worker.js`) still
  checks the library itself: its sessions are not navigable ones, so the
  bundle's keys do not match, and `Searcher` takes its cache from a
  directory. A bundle for its mode would be a second 14 MB file.

Measured in Node on the built WebAssembly (5 November 2026, load average
30–40; the browser was not timed, the budget of browser runs went on
correctness):

| `Aoc.Year2025.Day02` | before | after |
|---|---|---|
| server: first marks of the day's file | 2.1 s | 2.1–2.9 s |
| Check pane's answer (before: the page's `check_project`, 9.5 s, in a worker of its own after the page's outline; after: the server, all 8 own files published, announced) | 9.5 s | 4.2 s |
| `check_project` of the day in the page's session (the "Check every day" button's kind of work, and what Tests and Run do first) | 9.5 s | 2.6 s |
| `test_project` | 1.5 s | 1.5 s |
| `Aoc.Year2024.Day21`: first marks / Check pane's answer | 2.1 s / 5.2 s | 2.1 s / 2.4 s |

### 5.3 VS Code for the web, openvscode-server, vscode.dev

- **VS Code for the web** is the whole workbench in the browser (vscode.dev,
  github.dev), with extensions running in a web worker. A Stitchwort extension
  for it needs the language server as wasm (above) and a web build of the
  extension (`browser` entry point). Microsoft's hosted instances are theirs;
  self-hosting means building the `vscode-web` distribution (MIT source;
  Microsoft's product build carries different terms, **unverified**). Several
  MB of JavaScript and a stack of services.
- **openvscode-server** (Gitpod, MIT) runs VS Code in a browser against a
  *server-side* process. That means hosting a backend per user or per session,
  which is not a static page and not a playground.
- **When it makes sense:** a full workspace experience, such as "open the AoC
  project or the roguelike in VS Code in your browser", with multiple files, a
  terminal, and the real extension. It would be a separate "Open in VS Code
  for the web" offering (like github.dev for the repository), after a wasm
  language server exists. It does not replace the playground or the tour, and
  is out of scope for a single-snippet page.

## 6. Prototype

(Removed in SW-1378: `web/proto/codemirror.html`, `lsp.html` and their
entry modules are gone, the page being on the editor of §5.2.3.) The
prototype was `web/proto/codemirror.html` with `web/proto/codemirror-entry.js`,
`web/proto/package.json` (+ lockfile) and the built
`web/proto/codemirror.bundle.js`. It was not wired into the real page. It reused
the real `playground-worker.js` and `pkg/` unchanged.

What it shows: CM6 with line numbers, history, bracket closing, a toy
`StreamLanguage` tokenizer, a lint gutter, and the worker's `index` action:
the diagnostics become squiggles (2 errors and a goal as "info" for the `?`
in the sample), and hovering inside `n + n` shows `Nat` from the index's typed
expressions.

Checked in headless Chrome over the DevTools protocol: status line "3
diagnostic(s), 16 typed expressions"; lint ranges `"oops"` (error), `missing`
(error), `?` (info); hover tooltip `Nat`; 3 lint gutter markers.

To open it:

```
nix develop -c web/build.sh          # builds web/pkg/ if not built (about 2 min)
nix develop -c web/serve.sh --no-build
# open http://127.0.0.1:8000/proto/codemirror.html
```

To rebuild the bundle (the comment in the HTML has the command):
`cd web/proto && nix shell nixpkgs#nodejs nixpkgs#esbuild -c sh -c 'npm install
&& esbuild codemirror-entry.js --bundle --minify --format=esm --target=es2020
--outfile=codemirror.bundle.js'`.

Not shown: the real page's navigation, goals, projects or the Run view; the
prototype re-lints with `index` at 250 ms (CM6's `delay`) without
worker-termination for cancelling, and creates one worker for all requests.
It is a measurement, not a draft of the integration. The committed bundle can be
deleted with the prototype once the decision is made.

## 7. Recommendation

1. **Adopt CM6** for the playground, vendored and built in `web/build.sh` and
   the flake, not from a CDN. Reasons: 109 kB gzipped is 3% of the first
   load; each roadmap editor feature is an extension point; touch devices and
   screen readers are served by a contenteditable that the project documents;
   and it restyles from the page's own CSS variables, which matters for the
   tour.
2. **Do not use Monaco or VS Code in the playground.** Eight times the weight,
   documented as unsupported on mobile, IDE styling. The LSP reuse it offers is
   better obtained from the shared driver API in the roadmap; revisit only if a
   VS Code-for-the-web extension or a wasm language server is wanted
   independently.
3. **Keep a wasm language server as a separate, later question** (VS Code for
   the web, an "open the project in VS Code" link): it is not an editor
   decision and does not block CM6.
4. **Order**, if approved, after the tidy-ups (roadmap step 5):
   1. `crates/web` adds ranges to `check`'s diagnostics (S; also useful now),
      and `driver` hosts the position answers (roadmap step 1);
   2. build setup for the bundle, lockfile and Nix (S-M);
   3. the `source` façade, `EditorView`, colour via `colour()`, theme (M);
   4. lint marks, hover, navigation, library read-only view (M);
   5. browser tests ported (M);
   6. then completion (SW-1120), goals panel (roadmap 3), signature help on
      top, each S-M.
   About a week for the swap (steps 2-5), as the roadmap estimated.
5. **Keep the textarea page working until the swap is complete**, then remove
   it; do not maintain both. If a real phone shows CM6 is a regression, the
   textarea stays as a fallback chosen by a feature test (a decision for then).

## 8. Decisions for Matt

*Answered (D2415–D2428, 5 November 2026):* the JavaScript bundle is built
(esbuild and a lockfile, in `nix develop` and the flake; the output is not
committed); CM6, not Monaco or VS Code; colour through the existing tokenizer
(D2417); the editor on the shared language server, with page glue only where
the client has no UI (D2423), which settles squiggle ranges (they come from
the server); no phone check before the swap; `coi-serviceworker` shipped so
that cancellation works on GitHub Pages. The questions as they were put:

1. **May the playground build a JavaScript bundle at all?** (This is the real
   cost: `esbuild` and a lockfile in `web/build.sh`, the flake and CI.)
   Recommend yes, via `nix develop`/flake, with the output not committed.
2. **CM6 rather than Monaco/VS Code?** Recommend CM6.
3. **Syntax colouring approach:** reuse the existing tokenizer via decorations
   first (recommended), a `StreamLanguage` port, or a Lezer grammar?
4. **Is mobile editing required to match the textarea** before the swap, so
   that a phone test gates it? Recommend a real-device check of the prototype
   first (iOS Safari, Android Chrome), because this is the main thing I could
   not test.
5. **Squiggle ranges:** add ranges to `check`'s diagnostics in `crates/web`
   (recommended) rather than lint via `index` on every edit.
6. **Timing:** hold until the tidy-ups finish, per D2263, or do the S steps
   (ranges in `check`, the build setup) earlier because they stand alone?

## 9. Findings worth filing

- `crates/web` `check` diagnostics carry `line`/`column` but no end position;
  squiggles and "jump to" both want a range (the index already has them).
- `driver::live` building for wasm32 is still unchecked (roadmap open check);
  it gates a persistent worker session and any wasm language server.
- The page loads its font from Google Fonts: the playground is not fully
  offline-capable even though it is a static site; a vendored font (or system
  stack fallback) would make an offline mode a service-worker job.
- Browser tests assert on the textarea directly (`source.value`, selection);
  a `getText`/`setText` façade in the page would let them survive an editor
  swap.

## Sources

- npm registry, 3 Nov 2026: `https://registry.npmjs.org/<package>` for
  `codemirror`, `@codemirror/{state,view,commands,language,lint,autocomplete,
  search}`, `@lezer/{lr,highlight}`, `monaco-editor`, `monaco-languageclient`,
  `@codingame/monaco-vscode-api` (versions, `license`, `dist.unpackedSize`,
  publish times, dependencies).
- CodeMirror: `https://codemirror.net/` (system guide, reference manual for
  `@codemirror/lint`, `autocomplete`, `view`'s `hoverTooltip`, `Decoration`);
  not re-fetched during this evaluation, so API names are from the packages'
  installed typings and my knowledge: check against the manual when planning.
- Monaco: the README of `monaco-editor` 0.57.0 (the mobile answer); its
  accessibility guide is linked from it, **not read**.
- Measurements: esbuild 0.27.2 via `nix shell nixpkgs#esbuild`, gzip -9,
  brotli -q11 (nixpkgs), on the worktree's `web/build.sh` output.
