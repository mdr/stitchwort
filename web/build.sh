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
ls -lh web/pkg

mkdir -p web/pkg/aoc
cp aoc/day*.sw aoc/examples/day*.txt web/pkg/aoc/
{
  printf '['
  sep=""
  for file in aoc/day*.sw; do
    day="$(basename "$file" .sw)"
    number="${day#day}"
    number="${number#0}"
    printf '%s{"id":"aoc-%s","title":"AoC 2025 day %s","source":"%s.sw","input":"%s.txt"}' \
      "$sep" "$day" "$number" "$day" "$day"
    sep=","
  done
  printf ']\n'
} > web/pkg/aoc/index.json
