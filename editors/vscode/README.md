# Stitchwort VS Code extension (local)

Syntax colouring for `.sw` files, and a thin client for the language server
`stitchwort lsp` (design: `docs/proposals/language-server.md`).

## Features

- **Syntax colouring.** A TextMate grammar. Tokens follow
  `crates/syntax/src/lexer.rs` (keywords, `--` line comments, no block comments,
  `"` strings with `${…}` interpolation and escapes, and `'` chars with escapes)
  and the playground highlighter in `web/index.html`. If the lexer changes,
  update `syntaxes/stitchwort.tmLanguage.json`.
- `?` goal holes are highlighted; the language server shows each hole's goal on hover, in the diagnostic, and in the Goals panel.
- **From the server**, through the standard protocol: diagnostics as you type,
  go to definition, find references, hover, the outline, completion (locals,
  names in scope, members after a `.`, and library names that add their
  import), signature help in a
  call's arguments, the add-import quick fix on an unknown name, "Add the missing arms" on a non-exhaustive `match`, "Split `x` into its cases" on a variable of an arm, inlay hints
  for the type of a `let` whose type isn't written, and semantic colours for
  names the checker resolved (functions, types, constructors, variables,
  theorems, abilities). An `include`
  path is a document link to the included file. Nothing of these is
  computed in the extension.
- **Goals panel.** Run "Stitchwort: Show Goals" from the command palette: a
  panel opens beside the editor and follows the cursor, anywhere in the file
  (docs/proposals/goal-at-any-point.md, stages 1 and 3). It names the
  declaration, shows the names in scope with their types and `let` values, and
  then: `⊢ goal` in a proof, `expected T` for a program expression (with `has
  type U` below it when the expression's own type differs), `has type T` where
  only the type found is known. On a step of a proof (a `rewrite` rule, an
  arm's pattern, `match … with`, a `calc` line, a lambda's parameter, a `let`'s
  name, the `then` or `else` of `if h:`, the signature) it shows the goal
  before the step, a rewrite rule as used, and the goal after it in bold, with
  the names the step brings into scope marked `+`.
  On a `?` it asks `stitchwort/goalAt` 150 ms after the cursor or the text
  moves, and shows that hole's goal. Elsewhere it asks `stitchwort/contextAt`
  after the cursor has rested 300 ms (the server checks the file again, 0.3 to
  1.6 s on real files). An answer a later move has overtaken is dropped, and the
  previous answer stays until the next arrives. Where `contextAt` has nothing
  (a comment, a blank line) it shows the declaration's nearest `?` if it has
  one, else the last answer, dimmed. `?` goals are what the server already
  published as the blue diagnostics, so they also stay through an edit that
  doesn't parse. Not yet: Next/Previous Step commands, and highlighting the
  part of a goal a step changed.
- **Run icons** (SW-1121, D2513). The server offers code lenses
  (`textDocument/codeLens`, `crates/lsp/src/lens.rs`) in every `.sw` file, a
  single file outside a project too: "▶ Run test" above each `test`, "▶ Run
  tests" above the first test when the file has more than one, and "▶ Run"
  above `main`. The commands (`stitchwort.runTest`, `.runTests`, `.runMain`)
  are implemented here in `runs.js`. A test run is `stitchwort test FILE
  [--only NAME] --json` in the file's folder (the file is saved first); for a
  file of a project it is the file's namespace instead, `stitchwort test
  Aoc.Day01.Tests --json` in the project folder (the CLI refuses a project
  file on its own), and the results are narrowed to the file. The
  result is a message, the Output channel "Stitchwort Tests" lists each test
  and for a failure the two sides, and failed tests are marked as errors in
  the file until the next edit. "▶ Run" starts `stitchwort run FILE` in a
  terminal, so input works.
- **Testing panel** (D2245: project tests only). A Test Explorer controller,
  "Stitchwort", lists the tests of every `.sw` file under a `stitchwort.yaml`
  (project, then file, then test; listed by the server's `stitchwort/tests`
  request, or by reading the text if the server doesn't answer, and kept up
  to date as you type and as files change). Run, or Run Test at any level,
  runs `stitchwort test [NAMESPACE] [--only NAME] --json` in the project
  folder. Running a whole project splits it by namespace (the first three
  components, so one day of `aoc/` each), three runs at a time, and
  results appear as each run finishes; Stop kills the rest. A
  failure appears at the test's line (or at the false part of an `&&`) as a
  message with the two sides, shown as expected (right) and actual (left)
  when it is a comparison. A result from the cache has the description
  "cached" (and says so in the run's output). Debugging and coverage profiles
  are not offered.
- **Rename.** F2 renames a local, hypothesis, function or theorem in every
  file of the project, served by `stitchwort lsp` (`prepareRename`, `rename`).
  The renamed project is checked first: a rename that would cause an error or
  change what a declaration means is refused, with the problems listed. The
  server then offers a "Rename anyway" button (`window/showMessageRequest`),
  and on it applies the edit (`workspace/applyEdit`); the declarations whose
  meaning changed get a warning until the file is next edited. The extension
  has no code of its own for this.
- **Formatting.** Format Document and Format Selection work, served by
  `stitchwort lsp` (a file with a syntax error is left alone). Format on save is
  on for Stitchwort files (the extension's `configurationDefaults`); to turn it
  off, set `"[stitchwort]": { "editor.formatOnSave": false }`.
- **Library source.** Definitions in the standard library open as the real
  `std/` files when the server read std from a directory (the usual case in a
  checkout, or with `STITCHWORT_STD_DIR`). Such a file gets hover, go to
  definition and references like any other, but is not checked on its own: it
  is part of the library, which the server loads when it starts, so it has no
  diagnostics and edits to it apply after a restart. When std is the bundle
  embedded in the program, definitions open as read-only documents with the
  scheme `stitchwort-std:`, whose text comes from `stitchwort std-source` (run
  by the extension).

## Settings

Every optional feature has a switch in the settings (search for "Stitchwort"),
on unless noted (D3468):

| Setting | Effect |
| --- | --- |
| `stitchwort.inlayHints.letTypes` | the type after a `let` whose type isn't written |
| `stitchwort.codeLens.run` | the "▶ Run" and "▶ Run test" icons |
| `stitchwort.proofSearch.enabled` | "Search for a proof" on a `?` (and the "Split" quick fixes there) |
| `stitchwort.proofSearch.timeLimitMs` | how long one "Search for a proof" may run (default 5000) |
| `stitchwort.semanticColours` | colours from what the checker resolved each name to |
| `stitchwort.goals.openAutomatically` | open the Goals panel when a `.sw` file with a `?` opens (off by default) |
| `stitchwort.path` | the `stitchwort` program (restarts the server) |

The first five are sent to the server in `initializationOptions` and, when one
changes, in `workspace/didChangeConfiguration` (`{"settings": {"stitchwort":
…}}`; built by `serverSettings` in `client.js`). A feature that is off stays
advertised and is answered with nothing; the server then asks the editor to
refresh hints, lenses and colours. The Testing panel is not part of the run
icons setting.

## How the client finds and starts the server

On activation (a `.sw` file opens, or the workspace contains a
`stitchwort.yaml`) the extension starts `<stitchwort.path> lsp` with
`vscode-languageclient`, speaking LSP over stdio, with the first workspace
folder as the working directory. It serves `.sw` files on disk and
`stitchwort-std:` documents (bundle mode), and tells the server when a `stitchwort.yaml`
changes. Which project a file belongs to is the server's decision. The server's
log is in the "Stitchwort" output channel. Changing `stitchwort.path` restarts
it. If the program can't be run, a warning says so.

## The command line program

Build it and make it findable:

    cargo build --release -p stitchwort-cli     # in a checkout of this repo

and then either put `target/release` on PATH or set `stitchwort.path` in the
settings to the program (default `stitchwort`, looked up on PATH). It's a
machine-scoped setting, so a workspace can't redirect it.

## Install

    ./editors/vscode/install.sh

It installs the one npm dependency (`vscode-languageclient`, exact version in
`package.json` and `package-lock.json`), packages this folder as a `.vsix` and
runs `code --install-extension` (modern VS Code ignores folders symlinked into
`~/.vscode/extensions`). Then run "Developer: Reload Window". Rerun it after
changing the extension.

## Tests

    task test:vscode    # or: node --test "editors/vscode/test/*.test.js"

`client.js` (how the server is started, which documents it serves) doesn't
import `vscode`, so it is tested directly. `test/fake-server.js` is a tiny LSP
server over stdio with canned answers to the standard methods (full-text sync,
publishDiagnostics, definition, hover, references, documentSymbol); the tests
start it the way the client starts the real one. `task test:vscode` runs
`npm ci` first if `node_modules` is missing.

`runner.js` (the CLI arguments and JSON, finding a file's project, reading test
declarations) is tested against a stub program in `test/runner.test.js`; the
glue in `runs.js` is not.

The VS Code glue in `extension.js` isn't covered by tests (the Goals panel's
page body, `goalHtml`, is, in `client.js`).

### End-to-end check (with the real server)

Build the CLI, install the extension, open `aoc/` in VS Code, then: type an
error into a `.sw` file without saving and see the squiggle; F12 on a name,
Shift-F12 on a definition, hover on a use, and the outline (Cmd-Shift-O) give
the answers they gave before; write a `?` as a proof and run "Stitchwort: Show Goals": the panel shows the
goal, follows the cursor and updates as you type; F12 on a library name opens the library file
(a `stitchwort-std:` document in bundle mode); set `stitchwort.path` to a wrong path and see the warning. Open `docs/tutorial/01-proving-programs.sw`: "▶ Run test" appears above tests and works (a file outside a project); open `aoc/` and see the Testing panel list the days' tests, run one, and break one to see the failure at its line.

## Uninstall

    code --uninstall-extension local.stitchwort
