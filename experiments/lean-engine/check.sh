#!/usr/bin/env bash
# Checks the program, its tests, and one or both proof versions, with
# core Lean alone (no lake, no Mathlib). Compiled files go to a
# temporary folder outside the repo.
#   nix shell nixpkgs#lean4 -c ./check.sh [plain|idiomatic]...
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
versions=("$@")
[ ${#versions[@]} -eq 0 ] && versions=(plain idiomatic)

compile() { # source root, build root, module path
  mkdir -p "$(dirname "$2/$3")"
  lean -o "$2/$3.olean" "$1/$3.lean"
}

for version in "${versions[@]}"; do
  build="$(mktemp -d)"
  export LEAN_PATH="$build"
  start=$(date +%s.%N 2>/dev/null || date +%s)
  for module in Toy/Text Toy/Doc Toy/Print Toy/Tests; do
    compile "$here/program" "$build" "$module"
  done
  proofStart=$(date +%s.%N 2>/dev/null || date +%s)
  for module in Toy/Proofs/Readings Toy/Proofs/Words Toy/Proofs/Axioms; do
    compile "$here/$version" "$build" "$module"
  done
  end=$(date +%s.%N 2>/dev/null || date +%s)
  echo "$version: program and tests $(echo "$proofStart - $start" | bc) s, proofs $(echo "$end - $proofStart" | bc) s"
  rm -rf "$build"
done
