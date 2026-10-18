# Stitchwort VS Code extension (local)

Syntax colouring for `.sw` files. Grammar only, no runtime code. Tokens follow
`crates/syntax/src/lexer.rs` (keywords, `--` line comments, no block comments,
`"` strings and `'` chars with escapes) and the playground highlighter in
`web/index.html`. If the lexer changes, update `syntaxes/stitchwort.tmLanguage.json`.

## Install

    ln -s "$PWD/editors/vscode" ~/.vscode/extensions/stitchwort

Then run "Developer: Reload Window" in VS Code. (Cursor: `~/.cursor/extensions`.)

## Uninstall

    rm ~/.vscode/extensions/stitchwort

This removes only the symlink. Reload the window.
