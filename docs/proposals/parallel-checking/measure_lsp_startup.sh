#!/usr/bin/env bash
# The editor's start-up on tools/fmt with the project's check cache cold
# and the library's entries warm, start-up fill off and on, alternating
# (SW-4760, parallel-checking.md 9.9). Each run gets a fresh copy of the
# project whose cache holds only the library's entries (+nav+ty, as the
# editor writes them) from LIBRARY, a check cache folder this build wrote.
#
# A copied binary finds the library through STITCHWORT_STD_DIR.
#
# Usage: measure_lsp_startup.sh STITCHWORT LIBRARY WORK OUT [RUNS]
set -euo pipefail
stitchwort=$1 library=$2 work=$3 out=$4 runs=${5:-2}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
deep=src/Fmt/CommentsKeptProof.sw
mkdir -p "$work"
: > "$out"
for run in $(seq 1 "$runs"); do
  for workers in off auto; do
    project="$work/fmt-$workers-$run"
    rm -rf "$project"
    mkdir -p "$project/.stitchwort/cache/check"
    cp -R "$repo/tools/fmt/src" "$repo/tools/fmt/stitchwort.yaml" "$project/"
    cp "$library"/header "$library"/*-std.* "$project/.stitchwort/cache/check/"
    log="$work/fmt-$workers-$run.log"
    nice -n 19 python3 -I "$here/lsp_startup.py" "/usr/bin/time -l $stitchwort" \
      "$project" "$deep" "$workers" "$log" | tee -a "$out"
    peak=$(awk '/maximum resident set size/ {printf "%.2f", $1 / 1e9}' "$log")
    fill=$(grep -h "start-up fill" "$log" | sed 's/.*start-up fill, //' || true)
    echo "    peak ${peak} GB${fill:+; fill: $fill}" | tee -a "$out"
  done
done
