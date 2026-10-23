# Stitchwort VS Code extension (local)

Syntax colouring for `.sw` files, and a thin client for the language server
`stitchwort lsp` (design: `docs/proposals/language-server.md`).

## Features

- **Syntax colouring.** A TextMate grammar. Tokens follow
  `crates/syntax/src/lexer.rs` (keywords, `--` line comments, no block comments,
  `"` strings with `${…}` interpolation and escapes, and `'` chars with escapes)
  and the playground highlighter in `web/index.html`. If the lexer changes,
  update `syntaxes/stitchwort.tmLanguage.json`.
- `?` goal holes are highlighted; the language server shows each hole's goal on hover.
- **From the server**, through the standard protocol: diagnostics as you type,
  go to definition, find references, hover, and the outline. Nothing of these is
  computed in the extension.
- **Formatting.** Format Document and Format Selection work, served by
  `stitchwort lsp` (a file with a syntax error is left alone). Format on save is
  off, as in VS Code generally; to turn it on for Stitchwort files, add
  `"[stitchwort]": { "editor.formatOnSave": true }` to your settings.
- **Library source.** Definitions in the standard library open as read-only
  documents with the scheme `stitchwort-std:`, whose text comes from
  `stitchwort std-source` (run by the extension).

## How the client finds and starts the server

On activation (a `.sw` file opens, or the workspace contains a
`stitchwort.yaml`) the extension starts `<stitchwort.path> lsp` with
`vscode-languageclient`, speaking LSP over stdio, with the first workspace
folder as the working directory. It serves `.sw` files on disk and
`stitchwort-std:` documents, and tells the server when a `stitchwort.yaml`
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

    dev/t vscode        # or: node --test "editors/vscode/test/*.test.js"

`client.js` (how the server is started, which documents it serves) doesn't
import `vscode`, so it is tested directly. `test/fake-server.js` is a tiny LSP
server over stdio with canned answers to the standard methods (full-text sync,
publishDiagnostics, definition, hover, references, documentSymbol); the tests
start it the way the client starts the real one. `dev/t vscode` runs
`npm ci` first if `node_modules` is missing.

The VS Code glue in `extension.js` isn't covered by tests.

### End-to-end check (with the real server)

Build the CLI, install the extension, open `aoc/` in VS Code, then: type an
error into a `.sw` file without saving and see the squiggle; F12 on a name,
Shift-F12 on a definition, hover on a use, and the outline (Cmd-Shift-O) give
the answers they gave before; F12 on a library name opens a `stitchwort-std:`
document; set `stitchwort.path` to a wrong path and see the warning.

## Uninstall

    code --uninstall-extension local.stitchwort
