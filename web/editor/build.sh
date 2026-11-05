#!/usr/bin/env bash
# Bundles the playground's editor (CodeMirror 6 and its language-server
# client) into web/dist/ with esbuild. Run inside `nix develop`, which
# provides node and esbuild; `npm ci` installs the locked dependencies into
# web/editor/node_modules. Nix builds the same bundle (flake.nix, `editor`)
# from the same lockfile.
set -euo pipefail
# OUT is relative to the caller's folder, as `web/build.sh` passes it.
out="$(mkdir -p "${1:-$(dirname "$0")/../dist}" && cd "${1:-$(dirname "$0")/../dist}" && pwd)"
cd "$(dirname "$0")"
if [ "${SKIP_NPM_CI:-}" != 1 ]; then
  npm ci --no-audit --no-fund --silent
fi
esbuild src/editor-entry.js --bundle --minify --format=esm --target=es2020 \
  --outfile="$out/editor.bundle.js" --log-level=warning
ls -l "$out"
