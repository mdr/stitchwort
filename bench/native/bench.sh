#!/usr/bin/env bash
# `task native:bench`: the N1 measurement of docs/proposals/native-compilation.md.
# Scales the programs here up to the note's sizes and prints the best of
# ROUNDS wall times on the machine, `--js` and `--native`.
#
#   bash bench/native/bench.sh path/to/stitchwort [ROUNDS]
set -euo pipefail

SW=${1:?the stitchwort binary}
ROUNDS=${2:-3}
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=$HERE/../../target/native-bench
mkdir -p "$OUT"

# The note's sizes: 1,000,000 keys (i * 7919) % 1000000; 1,000,000 x 20
# non-tail calls; 20,000,000 tail iterations.
sed -e 's/keys 1000)/keys 1000000)/' -e 's/% 1009/% 1000000/' "$HERE/set_nat.sw" > "$OUT/set_nat.sw"
# The keys alone (built and counted), to take out of the `Set` time, as the
# note's section 1.2 does.
sed -e 's/Set.size (Set.fromList (keys 1000))/(keys 1000000).length/' -e 's/% 1009/% 1000000/' \
  "$HERE/set_nat.sw" > "$OUT/set_keys.sw"
sed -e 's/outer 1000 0/outer 1000000 0/' "$HERE/micro_call.sw" > "$OUT/micro_call.sw"
sed -e 's/spin 1000 0/spin 20000000 0/' "$HERE/micro_tail.sw" > "$OUT/micro_tail.sw"
sed -e 's/run 1000}/run 1000000}/' "$HERE/closures.sw" > "$OUT/closures.sw"
sed -e "s/bumps 1000 0/bumps 1000000 0/" -e "s/asks 1000 0/asks 1000000 0/" "$HERE/effects.sw" > "$OUT/effects.sw"

# Wall seconds of one run of `stitchwort run ARGS...` (its output discarded).
seconds() {
  local start end
  start=$(perl -MTime::HiRes=time -e 'printf "%.6f", time')
  "$SW" run "$@" > /dev/null
  end=$(perl -MTime::HiRes=time -e 'printf "%.6f", time')
  perl -e "printf '%.3f', $end - $start"
}

best() {
  local best="" t
  for _ in $(seq "$ROUNDS"); do
    t=$(seconds "$@")
    if [ -z "$best" ] || perl -e "exit !($t < $best)"; then best=$t; fi
  done
  echo "$best"
}

echo "load average: $(uptime | sed 's/.*load averages*: //')"
printf '%-12s %10s %10s %10s %8s\n' program machine --js --native speedup
for program in set_nat set_keys micro_call micro_tail closures effects; do
  file=$OUT/$program.sw
  # Check the answers agree before timing.
  a=$("$SW" run "$file"); b=$("$SW" run --native "$file")
  if [ "$a" != "$b" ]; then
    echo "$program: --native printed $b, the machine $a" >&2
    exit 1
  fi
  machine=$(best "$file")
  js=$(best --js "$file")
  native=$(best --native "$file")
  printf '%-12s %10s %10s %10s %7.1fx\n' "$program" "$machine" "$js" "$native" \
    "$(perl -e "print $machine / $native")"
  eval "times_$program=\"$machine $js $native\""
done
read -r sm sj sn <<< "$times_set_nat"
read -r km kj kn <<< "$times_set_keys"
ins_m=$(perl -e "printf '%.3f', $sm - $km")
ins_j=$(perl -e "printf '%.3f', $sj - $kj")
ins_n=$(perl -e "printf '%.3f', $sn - $kn")
printf '%-12s %10s %10s %10s %7.1fx\n' "inserts" "$ins_m" "$ins_j" "$ins_n" "$(perl -e "print $ins_m / $ins_n")"
echo "(inserts: set_nat minus set_keys, as section 1.2 of the note)"
echo "load average: $(uptime | sed 's/.*load averages*: //')"
