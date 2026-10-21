# Stitchwort VS Code extension (local)

Syntax colouring, go to definition, hover and an outline for `.sw` files.

## Features

- **Syntax colouring.** A TextMate grammar. Tokens follow
  `crates/syntax/src/lexer.rs` (keywords, `--` line comments, no block comments,
  `"` strings with `${…}` interpolation and escapes, and `'` chars with escapes)
  and the playground highlighter in `web/index.html`. If the lexer changes,
  update `syntaxes/stitchwort.tmLanguage.json`.
- **Go to definition** (F12, Cmd-click) on names: declarations, local variables
  (to their binder), constructors, fields, dot notation, and so on. Targets in
  the standard library open as read-only documents with the scheme
  `stitchwort-std:`, whose text comes from `stitchwort std-source`.
- **Hover** shows the type, and for a declaration its qualified name and kind.
- **Outline** (and breadcrumbs, Cmd-Shift-O) of a file's definitions, with
  constructors and fields nested under their type.

These come from the compiler's navigation index (`stitchwort check --index -`,
see `docs/proposals/code-navigation.md`). The extension runs it when a `.sw`
file is opened and (debounced) when one is saved, and keeps the last good index
per project, so lookups work while the file has errors, and reflect the file as
last saved, not unsaved edits. The project is the nearest folder above the file
with a `stitchwort.yaml` (the same rule as the command line); a file outside any
project is indexed on its own. Output from failed runs goes to the "Stitchwort"
output channel.

## The command line program

The extension runs the `stitchwort` CLI, so it must be built and findable:

    cargo build --release -p stitchwort-cli     # in a checkout of this repo

and then either put `target/release` on PATH or set `stitchwort.path` in the
settings to the program (default `stitchwort`, looked up on PATH). It's a
machine-scoped setting, so a workspace can't redirect it.

## Install

    ./editors/vscode/install.sh

It packages this folder as a `.vsix` and runs `code --install-extension`
(modern VS Code ignores folders symlinked into `~/.vscode/extensions`). Then
run "Developer: Reload Window". Rerun it after changing the extension.

## Tests

The lookup logic (position to reference, reference to location, outline
nesting) is in `navindex.js`, which doesn't import `vscode`:

    dev/t vscode        # or: node --test "editors/vscode/test/*.test.js"

It runs against `test/fixture/index.json`, made with the CLI from
`test/fixture/dot-notation.sw` (a copy of `examples/accept/dot-notation.sw`):

    cd editors/vscode/test/fixture && stitchwort check --index index.json dot-notation.sw

Regenerate it if the index format changes. The VS Code glue in `extension.js`
isn't covered by tests.

## Uninstall

    code --uninstall-extension local.stitchwort
