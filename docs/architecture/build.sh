#!/usr/bin/env bash
# Regenerates docs/architecture/crates.pdf from the workspace. Needs cargo, python3,
# graphviz and typst:
#   nix develop -c nix shell nixpkgs#graphviz nixpkgs#typst -c docs/architecture/build.sh
set -euo pipefail
cd "$(dirname "$0")"
../../dev/crate-graph --out crates.dot
dot -Tsvg crates.dot -o crates.svg
typst compile crates.typ crates.pdf \
  --input commit="$(git rev-parse --short HEAD)" --input date="$(date +%F)"
