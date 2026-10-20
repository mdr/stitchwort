#!/usr/bin/env bash
# Builds the playground's WebAssembly bundle into web/pkg/. Run inside
# `nix develop`, which provides wasm-bindgen and wasm-opt.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build -p stitchwort-web --target wasm32-unknown-unknown --release
wasm-bindgen --target web --no-typescript --out-dir web/pkg \
  target/wasm32-unknown-unknown/release/stitchwort_web.wasm
wasm-opt -Oz --enable-bulk-memory --enable-nontrapping-float-to-int \
  web/pkg/stitchwort_web_bg.wasm -o web/pkg/stitchwort_web_bg.wasm
# The AoC project's files, for the playground's Advent of Code group.
web/bundle-projects.sh . web/pkg
ls -lh web/pkg
