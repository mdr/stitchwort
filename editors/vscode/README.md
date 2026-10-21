# Stitchwort VS Code extension (local)

Syntax colouring, go to definition, find references, hover, an outline, workspace
symbols and error squiggles for `.sw` files.

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
- **Find All References** (Shift-F12) on a name: every use of the same declaration
  or local variable in the project, and the declaration itself when the editor asks
  for it. Uses inside the standard library are listed too.
- **Hover** shows the type, and for a declaration its qualified name and kind.
- **Outline** (and breadcrumbs, Cmd-Shift-O) of a file's definitions, with
  constructors and fields nested under their type.
- **Workspace symbols** (Cmd-T): the definitions of every indexed project, by
  qualified name (letters in order are enough: `shpdsc` finds
  `Shape.describe`). The library's definitions aren't offered.
- **Diagnostics**: the compiler's errors and warnings as squiggles and in the
  Problems panel, with its code (`E-TYPE-MISMATCH`), the explanation, notes, and
  related locations. They are replaced on each indexing run (open, save), and
  cleared for files that no longer have any. A diagnostic in a library file, or
  with no location, isn't shown.

These come from the compiler's navigation index (`stitchwort check --index -`,
see `docs/proposals/code-navigation.md`). The extension runs it when a `.sw`
file is opened and (debounced) when one is saved, and keeps the last good index
per project, so lookups work while the file has errors, and reflect the file as
last saved, not unsaved edits. The project is the nearest folder above the file
with a `stitchwort.yaml` (the same rule as the command line); a file outside any
project is indexed on its own. Output from failed runs goes to the "Stitchwort"
output channel. Diagnostics, like the rest, reflect the file as last saved.

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

Regenerate both indexes if the index format changes (`errors.sw` is a file with two
errors, for the diagnostics tests):

    cd editors/vscode/test/fixture && stitchwort check --index errors.json errors.sw

The fixture is for version 2. The VS Code glue in `extension.js`
isn't covered by tests.

## Uninstall

    code --uninstall-extension local.stitchwort
