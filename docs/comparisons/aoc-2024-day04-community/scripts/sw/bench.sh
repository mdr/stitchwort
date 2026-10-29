#!/bin/sh
# Time the scratch programs with `run` and `run --js`, and the native
# executables if they exist (NATIVE_DIR/native-MODULE).
# Usage: bench.sh PROJ INPUT STITCHWORT RUNS NATIVE_DIR MODULE...
T=$(dirname "$0")/../time4.sh
P=$1; IN=$2; SW=$3; RUNS=$4; ND=$5; shift 5
for m in "$@"; do
  echo "== $m run";  sh "$T" "$P" "$IN" "$RUNS" "$SW" run "Scratch.$m.main"
  echo "== $m js";   sh "$T" "$P" "$IN" "$RUNS" "$SW" run --js "Scratch.$m.main"
  if [ -x "$ND/native-$m" ]; then
    echo "== $m native"; sh "$T" "$P" "$IN" "$RUNS" "$ND/native-$m"
  fi
done
