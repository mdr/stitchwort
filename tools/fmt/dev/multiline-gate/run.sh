#!/usr/bin/env bash
# The multi-line read-back gate (SW-4121): generate slice 1 declarations in many layouts, run checks A and B on
# each, and print the counts. See README.md. Usage, from anywhere:
#   nix shell nixpkgs#python3 -c tools/fmt/dev/multiline-gate/run.sh [CHUNKS_PER_250] [WORK_DIR]
# CHUNKS_PER_250 scales the run: 1 (the default) is the full 22,000 files of SW-4121's note; 0 runs one chunk of
# each mode (1,250 files) and the hand cases, for a quick look.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
fmt=$(cd "$here/../.." && pwd)
bin=${STITCHWORT:-stitchwort}
scale=${1:-1}
work=${2:-$(mktemp -d)}
mkdir -p "$work/chunks" "$work/res"

# mode, chunks of 250 at full scale, first seed: SW-4121's run.
modes=(wild:40:1000 legal:20:2000 long:8:3000 noted:12:4000 longnoted:8:5000)
for entry in "${modes[@]}"; do
  IFS=: read -r mode chunks seed <<<"$entry"
  if [ "$scale" = 0 ]; then chunks=1; fi
  for i in $(seq 0 $((chunks - 1))); do
    python3 "$here/gen.py" $((seed + i)) 250 "$mode" "$work/chunks/$mode$i.cases"
  done
done
python3 "$here/hand.py" "$work/chunks/hand.cases" >/dev/null

cp "$here/MultilineGate.sw" "$fmt/src/MultilineGate.sw"
trap 'rm -f "$fmt/src/MultilineGate.sw"' EXIT
cd "$fmt"
for f in "$work"/chunks/*.cases; do
  name=$(basename "$f" .cases)
  for check in A B; do
    nice -n 19 "$bin" run "MultilineGate.main$check" <"$f" 2>&1 | grep -v '^note:' >"$work/res/$check.$name"
  done
done
python3 "$here/tally.py" "$work"
