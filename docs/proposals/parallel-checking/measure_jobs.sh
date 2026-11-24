#!/usr/bin/env bash
# The measure for stage 1 of parallel checking (docs/proposals/parallel-checking.md,
# section 9; SW-4718, for SW-4719's `check --jobs`). For the orchestrator's
# verifier or Overmind, not a lane: every run is a whole-project cold check.
# One at a time, on a quiet machine.
#
#   measure_jobs.sh STITCHWORT PROJECT OUT [JOBS...]
#
# STITCHWORT  a release binary (the checkout's own target/release/stitchwort)
# PROJECT     a project folder, e.g. tools/fmt or aoc
# OUT         a new folder for logs and caches (caches are deleted at the end)
# JOBS        job counts to try after 1; default "4 8"
#
# Three kinds of cold check, each with 1 job and then each JOBS:
#   cold     an empty cache: library and project both checked
#   libwarm  a cache holding only the library (`check --std Std` first)
#   nocache  --no-cache (D3731: the in-memory store when jobs > 1)
# For each run: wall seconds and peak memory (`time -l` is macOS's; use -v on
# Linux), and whether its output and its cache folder are byte for byte the
# 1-job run's. Output is compared without the "still checking" notes, which
# come in the order they happen (section 9.2).
#
# Machine time: about 9 cold checks of the project; for tools/fmt (110 to
# 146 s each on one job) about 12 minutes.
set -euo pipefail
bin=$(realpath "$1"); project=$(realpath "$2"); out=$3; shift 3
jobs_list=("$@"); [ ${#jobs_list[@]} -eq 0 ] && jobs_list=(4 8)
mkdir -p "$out"; out=$(realpath "$out")
cd "$project"

# run KIND JOBS CACHE_ARGS...: one timed check; logs in $out/KIND-JOBS.*
run() {
  local kind=$1 jobs=$2; shift 2
  local base="$out/$kind-$jobs"
  local status=0
  /usr/bin/time -l nice -n 10 "$bin" check --jobs "$jobs" "$@" \
    > "$base.stdout" 2> "$base.stderr.raw" || status=$?
  # `time -l` writes its figures after the check's own stderr.
  grep -vE '^note: still checking ' "$base.stderr.raw" \
    | grep -vE '^ *[0-9.]+ real|^ *[0-9]+  [a-z]' > "$base.stderr" || true
  local real mem
  real=$(grep -E '^ *[0-9.]+ real' "$base.stderr.raw" | awk '{print $1}')
  mem=$(grep 'maximum resident set size' "$base.stderr.raw" | awk '{printf "%.2f", $1/1e9}')
  printf '%-8s jobs %-2s  wall %7s s  peak %5s GB  exit %s\n' "$kind" "$jobs" "$real" "$mem" "$status"
  echo "$status" > "$base.exit"
}

# same KIND JOBS: compare a run's output (and cache, if it has one) with jobs 1.
same() {
  local kind=$1 jobs=$2 ok=yes
  cmp -s "$out/$kind-1.stdout" "$out/$kind-$jobs.stdout" || ok=no
  cmp -s "$out/$kind-1.stderr" "$out/$kind-$jobs.stderr" || ok=no
  cmp -s "$out/$kind-1.exit" "$out/$kind-$jobs.exit" || ok=no
  echo "         output same as jobs 1: $ok"
  if [ -d "$out/cache-$kind-1/check" ]; then
    if diff -rq "$out/cache-$kind-1/check" "$out/cache-$kind-$jobs/check" > "$out/$kind-$jobs.cachediff"; then
      echo "         cache same as jobs 1: yes ($(ls "$out/cache-$kind-1/check" | wc -l | tr -d ' ') files)"
    else
      echo "         cache same as jobs 1: NO, see $out/$kind-$jobs.cachediff"
    fi
  fi
}

# A cache folder with the library's entries only, and the salt every other
# cache here is given, so that entries can be compared byte for byte.
echo "== library fill (not timed against anything)"
lib="$out/cache-lib"
nice -n 10 "$bin" check --std --cache-dir "$lib" Std > "$out/libfill.txt" 2>&1 || echo "library fill exited $?"
seed() { # seed DIR [with-library]: a new cache folder with the shared salt
  mkdir -p "$1/check"
  if [ "${2:-}" = with-library ]; then cp -R "$lib/check/." "$1/check/"; else cp "$lib/check/header" "$1/check/header"; fi
}

for kind in cold libwarm nocache; do
  echo "== $kind"
  for jobs in 1 "${jobs_list[@]}"; do
    case $kind in
      cold)    seed "$out/cache-cold-$jobs";                 run cold "$jobs" --cache-dir "$out/cache-cold-$jobs" ;;
      libwarm) seed "$out/cache-libwarm-$jobs" with-library; run libwarm "$jobs" --cache-dir "$out/cache-libwarm-$jobs" ;;
      nocache) run nocache "$jobs" --no-cache ;;
    esac
    [ "$jobs" = 1 ] || same "$kind" "$jobs"
  done
done

# The three kinds should also agree with each other on what they report.
cmp -s "$out/cold-1.stdout" "$out/nocache-1.stdout" && cmp -s "$out/cold-1.stderr" "$out/nocache-1.stderr" \
  && echo "cold and nocache report the same (1 job)" || echo "cold and nocache DIFFER (1 job)"
rm -rf "$out"/cache-*
