#!/bin/sh
# Time a Stitchwort entry point on an input, a few runs, wall clock and peak memory.
# Usage: time4.sh AOC_DIR INPUT RUNS COMMAND ARGS...
# Example: time4.sh aoc aoc/inputs/2024/day04.txt 3 stitchwort run Aoc.Year2024.Day04.main
# Prints one line per run: seconds, peak RSS in MB, and the last output line.
dir=$1; input=$2; runs=$3; shift 3
i=0
while [ "$i" -lt "$runs" ]; do
  out=$( { cd "$dir" && /usr/bin/time -l "$@" < "$input"; } 2>&1 )
  secs=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
  rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{printf "%.0f", $1/1048576}')
  last=$(printf '%s\n' "$out" | grep -E '^Part 2' | tail -1)
  echo "${secs}s ${rss}MB  $last"
  i=$((i + 1))
done
