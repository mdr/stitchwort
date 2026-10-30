#!/bin/bash
# The queries of docs/proposals/search.md §4, run with the experimental
# `stitchwort dev search` (SW-915). From the repository root, after
# `task build`:
#
#   docs/proposals/search/queries.sh [CACHE_DIR] [extra flags, e.g. --no-filter]
#
# CACHE_DIR (default .stitchwort/search-cache) is the check cache the
# library loads through; the first run fills it.
set -u
CACHE=${1:-.stitchwort/search-cache}
shift || true
run() {
  echo "=== $1   [${*:2}]"
  dev/memguard --cap-gb 2 -- timeout 300 target/release/stitchwort dev search "$1" \
    --cache-dir "$CACHE" --repeat 5 --limit 5 "${@:2}" 2>&1
}
for q in \
  'List.length ((_: List _) ++ _) = _' \
  'List.length (_ ++ _) = _' \
  'List.length ((_: List _) ++ _)' \
  '_ ∈ List.map _ _' \
  '⊢ _ ∈ List.map _ _' \
  'Nat.min ?a ?b ≤ ?a' \
  'Nat.min _ _ ≤ _' \
  'Ord.compare ?x ?x = _' \
  '⊢ Not (Less = Greater)' \
  'List.count ?xs _ ≤ List.count ?xs _' \
  'List.zip ?xs (List.tailOf ?xs)' \
  '_ = _' \
  ; do
  run "$q" "$@"
done
run '"tailOf"' --defs "$@"
run 'List _ → List _' --defs "$@"
