#!/usr/bin/env bash
# Copies the AoC project into the playground's bundle (docs/proposals/
# playground-projects.md §5):
#   web/bundle-projects.sh REPO_ROOT OUT_DIR
# writes OUT_DIR/projects/aoc/{manifest.json,src/**/*.sw,examples/*.txt}.
# Only aoc/src/**/*.sw, aoc/examples/*.txt and aoc/inputs/*.txt are copied, by
# those patterns, never the whole aoc/ folder (D119: the puzzle inputs are
# bundled too). The script stops if a path falls outside those folders.
set -euo pipefail
export LC_ALL=C
root="$(cd "$1" && pwd)"
mkdir -p "$2"
dest="$(cd "$2" && pwd)/projects/aoc"

# The playground reads only the .sw files, so the config must say nothing
# else (D112).
if [ "$(cat "$root/aoc/stitchwort.yaml")" != "sources: [src]" ]; then
  echo "bundle-projects: aoc/stitchwort.yaml must be exactly 'sources: [src]'" >&2
  exit 1
fi

cd "$root/aoc"
files=$(find src -type f -name '*.sw' | sort)
examples=$(find examples inputs -maxdepth 1 -type f -name '*.txt' | sort)
for path in $files $examples; do
  case "$path" in
    /* | *..*)
      echo "bundle-projects: refusing to bundle '$path'" >&2
      exit 1
      ;;
    src/* | examples/* | inputs/*) ;;
    *)
      echo "bundle-projects: '$path' is outside src/, examples/ and inputs/" >&2
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

# One day per src/Aoc/DayNN/DayNN.sw, with its tests if src/Aoc/DayNN/Tests
# exists, its proofs if src/Aoc/DayNN/Proofs exists and its example input if
# examples/dayNN.txt exists.
{
  printf '{\n  "name": "aoc",\n  "title": "Advent of Code 2025",\n  "files": ['
  sep=""
  for path in $files; do
    printf '%s\n    "%s"' "$sep" "$path"
    sep=","
  done
  # The files `include` reads (the puzzle inputs and examples): sent to the compiler with
  # the sources, never shown or edited.
  printf '\n  ],\n  "data": ['
  sep=""
  for path in $(find inputs examples -maxdepth 1 -type f -name '*.txt' | sort); do
    printf '%s\n    "%s"' "$sep" "$path"
    sep=","
  done
  printf '\n  ],\n  "days": ['
  sep=""
  for program in $(find src/Aoc -mindepth 2 -maxdepth 2 -type f -name 'Day[0-9][0-9].sw' | sort); do
    day=$(basename "$program" .sw)
    n=${day#Day}
    namespaces="\"Aoc.$day\""
    if [ -d "src/Aoc/$day/Tests" ]; then
      namespaces="$namespaces, \"Aoc.$day.Tests\""
    fi
    if [ -d "src/Aoc/$day/Proofs" ]; then
      namespaces="$namespaces, \"Aoc.$day.Proofs\""
    fi
    inputs=""
    isep=""
    if [ -f "examples/day$n.txt" ]; then
      inputs="{ \"title\": \"Example\", \"path\": \"examples/day$n.txt\" }"
      isep=", "
    fi
    if [ -f "inputs/day$n.txt" ]; then
      inputs="$inputs$isep{ \"title\": \"Puzzle input\", \"path\": \"inputs/day$n.txt\" }"
    fi
    printf '%s\n    { "title": "Day %d", "open": "%s", "namespaces": [%s], "main": "Aoc.%s.main", "inputs": [%s] }' \
      "$sep" "$((10#$n))" "$program" "$namespaces" "$day" "$inputs"
    sep=","
  done
  printf '\n  ]\n}\n'
} >"$dest/manifest.json"
echo "bundled the AoC project into $dest"
