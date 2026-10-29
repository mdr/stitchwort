#!/bin/sh
# Time day 1 under `run`, `run --js` and the two executables, from aoc/.
# Usage: time.sh REPO_ROOT STITCHWORT SCRATCH [INPUT]
# SCRATCH holds day01-native and day01-plain, made beforehand with
#   stitchwort build [--native] Aoc.Year2024.Day01.main -o SCRATCH/day01-…
root=$1; sw=$2; scratch=$3; input=${4:-inputs/2024/day01.txt}
rb="$root/docs/comparisons/aoc-2024-day01-community/scripts/rb.py"
cd "$root/aoc" || exit 1
echo "run:";     command python3 -I "$rb" . "$input" 5 -- "$sw" run Aoc.Year2024.Day01.main
echo "run --js:"; command python3 -I "$rb" . "$input" 5 -- "$sw" run --js Aoc.Year2024.Day01.main
echo "native:";  command python3 -I "$rb" . "$input" 5 -- "$scratch/day01-native"
echo "build:";   command python3 -I "$rb" . "$input" 5 -- "$scratch/day01-plain"
