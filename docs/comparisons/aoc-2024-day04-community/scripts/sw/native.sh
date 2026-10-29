#!/bin/sh
# Build each scratch program as a native executable, OUT_DIR/native-MODULE.
# Usage: native.sh PROJ STITCHWORT OUT_DIR MODULE...
P=$1; SW=$2; OUT=$3; shift 3
for m in "$@"; do
  (cd "$P" && "$SW" build --native -o "$OUT/native-$m" "Scratch.$m.main" 2>&1 | tail -3)
done
