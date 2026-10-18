# Stitchwort VS Code extension (local)

Syntax colouring for `.sw` files. Grammar only, no runtime code. Tokens follow
`crates/syntax/src/lexer.rs` (keywords, `--` line comments, no block comments,
`"` strings and `'` chars with escapes) and the playground highlighter in
`web/index.html`. If the lexer changes, update `syntaxes/stitchwort.tmLanguage.json`.

## Install

    ./editors/vscode/install.sh

It packages this folder as a `.vsix` and runs `code --install-extension`
(modern VS Code ignores folders symlinked into `~/.vscode/extensions`). Then
run "Developer: Reload Window". Rerun it after changing the grammar.

## Uninstall

    code --uninstall-extension local.stitchwort
