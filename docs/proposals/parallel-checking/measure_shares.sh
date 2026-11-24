#!/usr/bin/env bash
# Measurements for docs/proposals/parallel-checking.md, "After proof
# irrelevance" (SW-4715). For the orchestrator's verifier or Overmind, not a
# lane: each is a whole-project check. One run at a time, on a quiet machine.
#
#   measure_shares.sh STITCHWORT PROJECT OUT [LIBRARY_DIR]
#
# STITCHWORT   a release binary (a copy also needs --std-dir: use the
#              checkout's own target/release/stitchwort)
# PROJECT      a project folder, e.g. tools/fmt or aoc
# OUT          a new folder for the tables
# LIBRARY_DIR  crates/elab/src/std, to class the library's declarations too
#
# It prints three things:
#  1. Today's namespace graph: work, critical path, bound, and the greedy
#     schedules (ns_graph.py). "bound" is the most namespace-level
#     parallelism (stage 1) can give on the project part.
#  2. How much of the time is theorems and how much everything else
#     (interface_share.py). "the rest" is a lower bound on a statements-first
#     pass; "largest single theorem" and the largest namespace bound what
#     checking proofs against statements (stage 3) can give.
#  3. The cost of loading the whole project from the cache with nothing left
#     out (wall seconds and peak memory of a warm check with
#     STITCHWORT_SKIP_UNNEEDED=0; `time -l` is macOS's, use `-v` on Linux):
#     what one worker pays, at most, to hold
#     everything.
set -euo pipefail
bin=$(realpath "$1"); project=$(realpath "$2"); out=$3; library=${4:-}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
mkdir -p "$out"; out=$(realpath "$out")
src="$project/src"
cd "$project"

echo "== cold check with per-declaration times"
STITCHWORT_STEP_PHASES=1 nice -n 10 "$bin" check --no-cache --timings=all 2> "$out/timings.txt" > "$out/check.txt" || echo "check exited $? (see $out/check.txt)"
python3 -I "$repo/docs/reviews/SW-4608/parse_timings.py" "$out/timings.txt" "$out" | head -3

echo "== 1. namespace graph"
python3 -I "$here/ns_graph.py" "$src" "$out/units.csv"

echo "== 2. theorems and the rest"
python3 -I "$here/interface_share.py" "$src${library:+,$library}" "$out/decls.csv" 15

echo "== 3. one full load from the cache"
cache="$out/cache"
nice -n 10 "$bin" check --cache-dir "$cache" > /dev/null 2>&1 || true
STITCHWORT_SKIP_UNNEEDED=0 /usr/bin/time -l nice -n 10 "$bin" check --cache-dir "$cache" 2> "$out/warm.txt" > /dev/null || true
grep -E "real|maximum resident" "$out/warm.txt"
rm -rf "$cache"
