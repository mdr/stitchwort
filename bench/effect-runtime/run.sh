#!/usr/bin/env bash
# Times bench/effect-runtime/map.sw (docs/proposals/effect-runtime.md) on the
# native runtime and on JS, for each variant and size given.
#
#   bench/effect-runtime/run.sh [native|js] VARIANT SIZE...
#
# Prints one line per run: backend, variant, size, wall seconds, and the
# program's last line of output, or the first line of its error. A run is stopped after
# $TIMEOUT seconds (default 120). Wall time includes checking the file
# (about the same for every run; see the note for the "0" row).
set -u
here="$(cd "$(dirname "$0")" && pwd)"
bin="${STITCHWORT:-$here/../../target/release/stitchwort}"
backend="$1"; shift
variant="$1"; shift
limit="${TIMEOUT:-120}"
# FILE=bench/effect-runtime/shapes.sw times that file's variants instead.
file="${FILE:-$here/map.sw}"
flag=""
if [ "$backend" = js ]; then flag="--js"; fi
for size in "$@"; do
  start=$(date +%s.%N 2>/dev/null || python3 -c 'import time; print(time.time())')
  out=$(printf '%s\n%s\n' "$variant" "$size" | timeout "$limit" "$bin" run $flag "$file" 2>&1)
  code=$?
  end=$(date +%s.%N 2>/dev/null || python3 -c 'import time; print(time.time())')
  secs=$(echo "$end - $start" | bc)
  if [ $code -eq 124 ]; then out="timeout after ${limit}s"; fi
  # The answer is the last line; an error's first line says what went wrong.
  if [ $code -eq 0 ]; then line="$(echo "$out" | tail -1)"; else line="$(echo "$out" | grep -v '^$' | head -1)"; fi
  printf '%s\t%s\t%s\t%.2f\t%s\n' "$backend" "$variant" "$size" "$secs" "$line"
done
