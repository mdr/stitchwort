#!/bin/sh
# Collect the GitHub repositories cited in the earlier community notes (days 6-8),
# one line OWNER/REPO each, as the seed list for day 9.
# Usage: seed.sh REPO_ROOT OUT
root=$1; out=$2
grep -ho 'https://github\.com/[^/)]*/[^/)]*/blob/[^)]*' \
  "$root"/docs/comparisons/aoc-day0[5-8]-community.md \
  | awk -F/ '{print $4"/"$5}' | sort -u > "$out"
wc -l < "$out"
