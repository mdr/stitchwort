#!/usr/bin/env bash
# Writes the standard library as one file the playground fetches beside the
# WebAssembly (docs/proposals/std-as-data.md):
#   web/bundle-std.sh REPO_ROOT OUT_DIR
# writes OUT_DIR/std.bundle: for each `.sw` file under crates/elab/src/std
# and the core's manifest core/order.txt, sorted by path, a header line
# `path bytes` and then that many bytes of the file (no escaping). The
# compiler reads it with `load_std` (`stitchwort_elab::use_std_bundle`).
set -euo pipefail
export LC_ALL=C
root="$(cd "$1" && pwd)"
mkdir -p "$2"
out="$(cd "$2" && pwd)/std.bundle"
cd "$root/crates/elab/src/std"
: >"$out"
for path in $(find . -type f \( -name '*.sw' -o -path ./core/order.txt \) | sed 's|^\./||' | sort); do
  printf '%s %s\n' "$path" "$(wc -c <"$path" | tr -d ' ')" >>"$out"
  cat "$path" >>"$out"
done
echo "bundled the standard library into $out"
