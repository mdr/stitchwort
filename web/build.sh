#!/usr/bin/env bash
# Builds the playground's WebAssembly bundle into web/pkg/ and the editor's
# JavaScript bundle into web/dist/. Run inside `nix develop`, which provides
# wasm-bindgen, wasm-opt, node and esbuild.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build -p stitchwort-web --target wasm32-unknown-unknown --release
wasm-bindgen --target web --no-typescript --out-dir web/pkg \
  target/wasm32-unknown-unknown/release/stitchwort_web.wasm
wasm-opt -Oz --enable-bulk-memory --enable-nontrapping-float-to-int \
  web/pkg/stitchwort_web_bg.wasm -o web/pkg/stitchwort_web_bg.wasm
# The standard library, fetched beside the WebAssembly.
web/bundle-std.sh . web/pkg
# The library checked by that WebAssembly, so the language server replays it
# (pkg/std.cache; a minute or two, most of it the files that fail to check
# under the worker's limits).
node web/bundle-std-cache.mjs web/pkg
# The AoC project's files, for the playground's Advent of Code group.
web/bundle-projects.sh . web/pkg
# The editor (CodeMirror 6 and the language-server client), from web/editor/.
web/editor/build.sh web/dist
# pkg/version.json: the content hashes the page caches by (docs/proposals/
# playground-projects.md §10.2); it covers the editor's bundle, so it comes after.
web/write-version.sh web
ls -lh web/pkg web/dist
