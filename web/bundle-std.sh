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
# Written beside it and renamed into place, so two builds at once (a
# verifier's and another job's) can't interleave their writes: they once
# made a bundle that started part way through a file, which the compiler
# refused ("bad length in the bundle header").
part="$(mktemp "$out.XXXXXX")"
trap 'rm -f "$part"' EXIT
cd "$root/crates/elab/src/std"
for path in $(find . -type f \( -name '*.sw' -o -path ./core/order.txt \) | sed 's|^\./||' | sort); do
  printf '%s %s\n' "$path" "$(wc -c <"$path" | tr -d ' ')" >>"$part"
  cat "$path" >>"$part"
done
chmod 644 "$part"
mv "$part" "$out"
trap - EXIT
echo "bundled the standard library into $out"
