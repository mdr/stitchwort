#!/bin/sh
# Time the scratch programs (sw/) under `run` and `run --js` in the scratch
# project PROJ (sources: [src, aocsrc], with aocsrc linked to aoc/src and
# sw/*.sw copied to src/Scratch/), on INPUT.
# Usage: time-alt.sh PROJ STITCHWORT INPUT [NAME ...]
proj=$1; sw=$2; input=$3; shift 3
rb="$(dirname "$0")/rb.py"
[ $# -gt 0 ] || set -- Hello Spec Words
for name in "$@"; do
  for mode in "" --js; do
    echo "$name run $mode:"
    command python3 -I "$rb" "$proj" "$input" 3 -- "$sw" run $mode "Scratch.$name.main"
  done
done
