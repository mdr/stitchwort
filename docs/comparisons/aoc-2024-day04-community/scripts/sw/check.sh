#!/bin/sh
# Check and run each scratch program once on the real input.
# Usage: check.sh PROJ INPUT STITCHWORT [MODULE...]
P=$1; IN=$2; SW=$3; shift 3
for m in "$@"; do
  echo "== $m"
  (cd "$P" && "$SW" run "Scratch.$m.main" < "$IN" 2>&1 | head -12)
done
