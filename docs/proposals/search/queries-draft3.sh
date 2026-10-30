#!/bin/bash
# The measurements of docs/proposals/search.md draft 3 (§6), run with the
# experimental `stitchwort dev search` (SW-915). From the repository root,
# after `task build`:
#
#   docs/proposals/search/queries-draft3.sh [CACHE_DIR] [SECTION...]
#
# SECTION is one or more of: self left uses hand (default: all). CACHE_DIR
# (default .stitchwort/search-cache) is the check cache the library loads
# through; the first run fills it. `self` takes about a minute and a half,
# `left` a minute, `uses` about twelve minutes, on a shared machine.
#
# Directives (parts of the query string): `tiers:on` (draft 3's relations,
# §5.1), `ho:on` (targets headed by a theorem variable, §5.2), `iff:on`
# (`Iff` sides in rewrite mode), `data:on` (data types in the filter),
# `filter:off|either`, `relax:off` (no relaxed second pass), `rank:NAME`.
set -u
CACHE=${1:-.stitchwort/search-cache}
shift || true
SECTIONS=${*:-self left uses hand}
run() {
  echo "=== $1   [${*:2}]"
  dev/memguard --cap-gb 2 -- timeout 1800 target/release/stitchwort dev search "$1" \
    --cache-dir "$CACHE" --limit 6 "${@:2}" 2>&1 | grep -v '^pattern:'
}
D3='tiers:on, ho:on'
for section in $SECTIONS; do
  case $section in
  self)
    # §6.1: every std theorem's conclusion as a pattern.
    run 'self:conclusion'
    run 'self:conclusion, tiers:on'
    run "self:conclusion, $D3"
    run "self:conclusion, $D3, data:on"
    run "self:conclusion, $D3, filter:off"
    ;;
  left)
    # §6.1: every equation's (and with iff:on, Iff's) left side.
    run 'self:left'
    run "self:left, $D3"
    run "self:left, $D3, iff:on"
    run "self:left, $D3, iff:on, data:on"
    run "self:left, $D3, filter:off"
    ;;
  uses)
    # §6.2: the proof-use benchmark.
    run 'self:uses, relax:off'
    run 'self:uses'
    run "self:uses, $D3"
    run "self:uses, $D3, data:on"
    run "self:uses, $D3, filter:either"
    run "self:uses, $D3, filter:off"
    ;;
  hand)
    # §6.3: draft 1's hand queries and draft 2's others.
    for r in proposed tiered; do
      for q in 'List.length ((_: List _) ++ _) = _' '_ ∈ List.map _ _' 'Nat.min _ _ ≤ _' \
        'Ord.compare ?x ?x = _' '⊢ Not (Less = Greater)'; do
        run "rank:$r, $D3, $q"
      done
    done
    for q in '(_: Nat) ≤ _ → _ ≤ _ → _ ≤ _' '(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c' \
      'List _ → Nat → List _' 'Nat → List _ → List _' 'List ?a → Nat → List ?a'; do
      run "$D3, mode:subset, $q" --defs
    done
    run "$D3, data:on, mode:subset, List ?a → Nat → List ?a" --defs
    for q in 'List.length (List.append _ _)' 'List.map (List.map _ _) _' 'Ord.compare ?x ?x' \
      '(_: Nat) + 0'; do
      run "$D3, mode:rewrite, $q"
    done
    run "$D3, mode:rewrite, iff:on, _ ∈ List.append _ _"
    for q in 'Ord.compare (?x: Nat) ?x = _' 'List.sort _ = _' 'DecEq.decide _ _' \
      '⊢ List.length (List.append ?xs ?ys) = List.length ?xs + List.length ?ys'; do
      run "$D3, $q"
    done
    run "$D3, Ord.compare ?x ?x = _" --json
    ;;
  esac
done
