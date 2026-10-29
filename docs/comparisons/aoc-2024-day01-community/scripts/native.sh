#!/bin/sh
# Build each scratch entry point natively in PROJ, then time it on INPUT.
# Usage: native.sh PROJ STITCHWORT INPUT FULL.NAME ...
proj=$1; sw=$2; input=$3; shift 3
rb="$(cd "$(dirname "$0")" && pwd)/rb.py"
mkdir -p "$proj/bin"
for name in "$@"; do
  exe="$proj/bin/$name"
  [ -x "$exe" ] || (cd "$proj" && "$sw" build --native "$name" -o "$exe" >/dev/null 2>&1) || { echo "$name: build failed"; continue; }
  printf '%s native: ' "$name"
  command python3 -I "$rb" "$proj" "$input" 3 -- "$exe"
done
