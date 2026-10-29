#!/bin/sh
# Time native executables only: each NATIVE_DIR/native-MODULE, and any
# further executables given by path.
# Usage: nbench.sh DIR INPUT RUNS EXECUTABLE...
T=$(dirname "$0")/../time4.sh
D=$1; IN=$2; RUNS=$3; shift 3
for x in "$@"; do
  echo "== $(basename "$x")"; sh "$T" "$D" "$IN" "$RUNS" "$x"
done
