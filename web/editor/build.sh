#!/usr/bin/env bash
# Bundles the playground's editor (CodeMirror 6 and its language-server
# client) into web/dist/ with esbuild. Run inside `nix develop`, which
# provides node and esbuild; `npm ci` installs the locked dependencies into
# web/editor/node_modules. Nix builds the same bundle (flake.nix, `editor`)
# from the same lockfile.
set -euo pipefail
cd "$(dirname "$0")"
if [ "${SKIP_NPM_CI:-}" != 1 ]; then
  npm ci --no-audit --no-fund --silent
fi
out="${1:-../dist}"
mkdir -p "$out"
for entry in lsp codemirror; do
  esbuild "src/$entry-entry.js" --bundle --minify --format=esm --target=es2020 \
    --outfile="$out/$entry.bundle.js" --log-level=warning
done
ls -l "$out"
