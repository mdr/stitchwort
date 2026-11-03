# Evaluation: an editor component for the playground

**Status:** evaluation for Matt (SW-1118, D2241, D2263), 3 November 2026.
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

`web/proto/codemirror.html` with `web/proto/codemirror-entry.js`,
`web/proto/package.json` (+ lockfile) and the built
`web/proto/codemirror.bundle.js`. It is not wired into the real page. It reuses
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
