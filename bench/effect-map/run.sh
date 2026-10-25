#!/usr/bin/env bash
# Times bench/effect-map/map.sw on the fast runtime and in Node, for each
# mode and list length. Usage, from the repository root, after
# `cargo build --release -p stitchwort-cli`:
#   nix develop -c bench/effect-map/run.sh [LENGTH...]
# Each line is: backend mode length rounds seconds checksum, the best of
# `RUNS` (default 3) runs of `stitchwort run` (with `--js` for Node). Each length maps
# 10,000,000 elements in all. The `setup` line is the same run with no
# rounds (checking, code generation and building the list), to subtract.
# `MODES` picks the modes (default `setup sum map fail`; also `filter`,
# `fold` and `any`); `SW` and `SRC` override the binary and the source, to
# compare with another build.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
sw="${SW:-$root/target/release/stitchwort}"
src="${SRC:-$root/bench/effect-map/map.sw}"
if [ $# -eq 0 ]; then set -- 100000 1000000; fi

best() {
  local input=$1
  shift
  local best="" result=""
  for _ in $(seq "${RUNS:-3}"); do
    local start end t
    start=$(perl -MTime::HiRes=time -e 'printf "%.3f", time')
    result=$(echo "$input" | "$@")
    end=$(perl -MTime::HiRes=time -e 'printf "%.3f", time')
    t=$(echo "$end - $start" | bc)
    if [ -z "$best" ] || (($(echo "$t < $best" | bc))); then best=$t; fi
  done
  echo "$best $result"
}

for n in "$@"; do
  rounds=$((10000000 / n))
  ((rounds < 1)) && rounds=1
  for mode in ${MODES:-setup sum map fail}; do
    r=$rounds m=$mode
    [ "$mode" = setup ] && r=0 m=map
    echo "rt $mode $n $r $(best "$m $n $r" "$sw" run "$src")"
    echo "js $mode $n $r $(best "$m $n $r" "$sw" run --js "$src")"
  done
done
