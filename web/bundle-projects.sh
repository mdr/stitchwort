#!/usr/bin/env bash
# Copies the AoC project and the roguelike into the playground's bundle
# (docs/proposals/playground-projects.md §5):
#   web/bundle-projects.sh REPO_ROOT OUT_DIR
# writes OUT_DIR/projects/aoc/{manifest.json,src/**/*.sw,examples/*.txt,...}
# and OUT_DIR/projects/rogue/{manifest.json,src/**/*.sw}.
# Only aoc/src/**/*.sw, aoc/examples/*.txt and aoc/inputs/*.txt are copied, by
# those patterns, never the whole aoc/ folder (D119: the puzzle inputs are
# bundled too). The roguelike (games/rogue) gets only its src/**/*.sw. The
# script stops if a path falls outside those folders.
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

# ---- The roguelike (games/rogue): its sources only. --------------------------
rogue_dest="$(dirname "$dest")/rogue"
if [ "$(cat "$root/games/rogue/stitchwort.yaml")" != "sources: [src]" ]; then
  echo "bundle-projects: games/rogue/stitchwort.yaml must be exactly 'sources: [src]'" >&2
  exit 1
fi
cd "$root/games/rogue"
rogue_files=$(find src -type f -name '*.sw' | sort)
for path in $rogue_files; do
  case "$path" in
    /* | *..*)
      echo "bundle-projects: refusing to bundle '$path'" >&2
      exit 1
      ;;
    src/*) ;;
    *)
      echo "bundle-projects: '$path' is outside src/" >&2
      exit 1
      ;;
  esac
done
rm -rf "$rogue_dest"
mkdir -p "$rogue_dest"
for path in $rogue_files; do
  mkdir -p "$rogue_dest/$(dirname "$path")"
  cp "$path" "$rogue_dest/$path"
done
# Two entries for Rogue.main, with its tests and proofs: "Play" runs live in
# the terminal pane; "Play (scripted)" keeps the input box, which starts as a
# short key script.
{
  printf '{\n  "name": "rogue",\n  "title": "Roguelike",\n  "files": ['
  sep=""
  for path in $rogue_files; do
    printf '%s\n    "%s"' "$sep" "$path"
    sep=","
  done
  printf '\n  ],\n  "data": [],\n  "days": [\n'
  printf '    { "title": "Play", "open": "src/Rogue/Rogue.sw", "namespaces": ["Rogue", "Rogue.Tests", "Rogue.Proofs"], "main": "Rogue.main", "inputs": [], "live": true,\n'
  printf '      "evalInput": "Rogue.ending",\n'
  printf '      "hint": "Run opens a terminal: click it if it has not got the keys, then play. Arrows, h/j/k/l or a/s/w/d move, > goes down stairs, p drinks a potion, . waits, q quits; walking into a monster attacks it. Ctrl-C stops the game; Esc then Tab leaves the terminal." },\n'
  printf '    { "title": "Play (scripted)", "open": "src/Rogue/Rogue.sw", "namespaces": ["Rogue", "Rogue.Tests", "Rogue.Proofs"], "main": "Rogue.main", "inputs": [],\n'
  printf '      "defaultInput": "lllj.q",\n'
  printf '      "evalInput": "Rogue.ending",\n'
  printf '      "hint": "Type keys into the input box, then Run: h/j/k/l, a/s/w/d or the arrow keys move, > goes down stairs, p drinks a potion, . waits, q quits; walking into a monster attacks it. Other keys are skipped, and the end of the input quits. Every turn prints a frame." }\n'
  printf '  ]\n}\n'
} >"$rogue_dest/manifest.json"
echo "bundled the roguelike into $rogue_dest"
