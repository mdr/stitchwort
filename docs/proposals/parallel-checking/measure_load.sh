#!/usr/bin/env bash
# One whole-project load from a warm check cache: wall time and peak memory,
# with proofs and (once stage 2 of parallel checking exists) without.
# For the orchestrator or Overmind, not a lane: it runs a cold whole-project
# check first to fill the cache.
#
#   measure_load.sh BINARY PROJECT_DIR OUT_DIR
#
# Section 10.6 of docs/proposals/parallel-checking.md says how to read it.
set -euo pipefail
bin=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
project=$2
out=$3
mkdir -p "$out"
out=$(cd "$out" && pwd)
cache="$out/cache"
rm -rf "$cache"
cd "$project"

echo "== filling the cache (a cold check)"
/usr/bin/time -l nice -n 10 "$bin" check --cache-dir "$cache" > /dev/null 2> "$out/cold.txt" || true
grep -E "real|maximum resident" "$out/cold.txt"

# STITCHWORT_SKIP_UNNEEDED=0 makes a plain check load every namespace
# instead of reporting clean ones from their entries unloaded.
for proofs in 1 0; do
    echo "== one whole load, STITCHWORT_LOAD_PROOFS=$proofs (0 means nothing before stage 2)"
    for run in 1 2 3; do
        STITCHWORT_LOAD_PROOFS=$proofs STITCHWORT_SKIP_UNNEEDED=0 \
            /usr/bin/time -l nice -n 10 "$bin" check --cache-dir "$cache" \
            > /dev/null 2> "$out/load-$proofs-$run.txt" || true
        grep -E "real|maximum resident" "$out/load-$proofs-$run.txt" | tr '\n' ' '
        echo
    done
done
rm -rf "$cache"
