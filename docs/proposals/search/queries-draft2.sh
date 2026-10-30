#!/bin/bash
# The measurements of docs/proposals/search.md draft 2 (§6), run with the
# experimental `stitchwort dev search` (SW-915). From the repository root,
# after `task build`:
#
#   docs/proposals/search/queries-draft2.sh [CACHE_DIR] [SECTION...]
#
# SECTION is one or more of: self order rewrite instances ranking (default:
# all). CACHE_DIR (default .stitchwort/search-cache) is the check cache the
# library loads through; the first run fills it.
set -u
CACHE=${1:-.stitchwort/search-cache}
shift || true
SECTIONS=${*:-self order rewrite instances ranking}
run() {
  echo "=== $1   [${*:2}]"
  dev/memguard --cap-gb 2 -- timeout 900 target/release/stitchwort dev search "$1" \
    --cache-dir "$CACHE" --limit 6 "${@:2}" 2>&1 | grep -v '^pattern:'
}
for section in $SECTIONS; do
  case $section in
  self)
    # §6.1: every std theorem's conclusion, and every equation's left side,
    # as a pattern; with and without the constants filter.
    run 'self:conclusion'
    run 'self:conclusion' --no-filter
    run 'self:left'
    run 'self:left' --no-filter
    ;;
  order)
    # §6.2: argument order. `--defs` searches definitions too.
    for q in \
      'List ?a → Nat → List ?a' \
      'Nat → List ?a → List ?a' \
      'mode:permute, List ?a → Nat → List ?a' \
      'mode:permute, Nat → List ?a → List ?a' \
      'mode:subset, Nat → List ?a → List ?a' \
      'List _ → Nat → List _' \
      'mode:permute, List _ → Nat → List _' \
      'mode:subset, List _ → Nat → List _' \
      '(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _' \
      'mode:permute, (_: Nat) ≤ _ → _ ≤ _ → _ ≤ _' \
      'mode:subset, (_: Nat) ≤ _ → _ ≤ _ → _ ≤ _' \
      'mode:subset, _ ≤ ?b → (_: Nat) ≤ _ → _ ≤ _' \
      'Nat → List _ → List _' \
      'mode:permute, Nat → List _ → List _' \
      'mode:subset, Nat → List _ → List _' \
      ; do
      run "$q" --defs
    done
    ;;
  rewrite)
    # §6.3: rewrite search (the sides of a stated equation).
    for q in \
      'mode:rewrite, List.length (List.append _ _)' \
      'mode:rewrite, List.map _ (List.map _ _)' \
      'mode:rewrite, List.map (List.map _ _) _' \
      'mode:rewrite, Ord.compare ?x ?x' \
      'mode:rewrite, (_: Nat) + 0' \
      'mode:rewrite, List.reverse (List.reverse _)' \
      'List.length (List.append _ _)' \
      ; do
      run "$q"
    done
    ;;
  instances)
    # §6.4: instance arguments and generic functions.
    for q in \
      'Ord.compare ?x ?x = _' \
      'Ord.compare (?x: Nat) ?x = _' \
      'Nat.compare ?x ?x = _' \
      'List.sort _ = _' \
      'List.Sorted (List.sort _)' \
      'List.Sorted _ (List.sort _)' \
      'DecEq.decide _ _' \
      'Show.toText _' \
      'Show.toText (_: Nat)' \
      '(_: Nat) < _ → _' \
      ; do
      run "$q"
    done
    ;;
  ranking)
    # §6.1: draft 1's queries under each ranking.
    for r in draft1 proposed isabelle rocq loogle; do
      for q in \
        'List.length ((_: List _) ++ _) = _' \
        '_ ∈ List.map _ _' \
        'Nat.min _ _ ≤ _' \
        'Ord.compare ?x ?x = _' \
        '⊢ Not (Less = Greater)' \
        ; do
        run "rank:$r, $q"
      done
    done
    ;;
  esac
done
