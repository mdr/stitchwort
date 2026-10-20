#!/usr/bin/env bash
# Copies the AoC project into the playground's bundle (docs/proposals/
# playground-projects.md §5):
#   web/bundle-projects.sh REPO_ROOT OUT_DIR
# writes OUT_DIR/projects/aoc/{manifest.json,src/**/*.sw,examples/*.txt}.
# Only aoc/src/**/*.sw and aoc/examples/*.txt are copied, by those patterns;
# aoc/inputs/ (the private puzzle inputs) is never read, and the script stops
# if any path it would bundle contains `inputs/`.
set -euo pipefail
export LC_ALL=C
root="$1"
dest="$2/projects/aoc"

# The playground reads only the .sw files, so the config must say nothing
# else (D112).
if [ "$(cat "$root/aoc/stitchwort.yaml")" != "sources: [src]" ]; then
  echo "bundle-projects: aoc/stitchwort.yaml must be exactly 'sources: [src]'" >&2
  exit 1
fi

cd "$root/aoc"
files=$(find src -type f -name '*.sw' | sort)
examples=$(find examples -maxdepth 1 -type f -name '*.txt' | sort)
for path in $files $examples; do
  case "$path" in
    *inputs/* | /* | *..*)
      echo "bundle-projects: refusing to bundle '$path'" >&2
      exit 1
      ;;
    src/* | examples/*) ;;
    *)
      echo "bundle-projects: '$path' is outside src/ and examples/" >&2
      exit 1
      ;;
  esac
done

rm -rf "$dest"
mkdir -p "$dest"
for path in $files $examples; do
  mkdir -p "$dest/$(dirname "$path")"
  cp "$path" "$dest/$path"
done

# One day per src/Aoc/DayNN/DayNN.sw, with its proofs if src/Aoc/DayNN/Proofs
# exists and its example input if examples/dayNN.txt exists.
{
  printf '{\n  "name": "aoc",\n  "title": "Advent of Code 2025",\n  "files": ['
  sep=""
  for path in $files; do
    printf '%s\n    "%s"' "$sep" "$path"
    sep=","
  done
  printf '\n  ],\n  "days": ['
  sep=""
  for program in $(find src/Aoc -mindepth 2 -maxdepth 2 -type f -name 'Day[0-9][0-9].sw' | sort); do
    day=$(basename "$program" .sw)
    n=${day#Day}
    namespaces="\"Aoc.$day\""
    if [ -d "src/Aoc/$day/Proofs" ]; then
      namespaces="$namespaces, \"Aoc.$day.Proofs\""
    fi
    input=""
    if [ -f "examples/day$n.txt" ]; then
      input=", \"input\": \"examples/day$n.txt\""
    fi
    printf '%s\n    { "title": "Day %d", "open": "%s", "namespaces": [%s], "main": "Aoc.%s.main"%s }' \
      "$sep" "$((10#$n))" "$program" "$namespaces" "$day" "$input"
    sep=","
  done
  printf '\n  ]\n}\n'
} >"$dest/manifest.json"
echo "bundled the AoC project into $dest"
