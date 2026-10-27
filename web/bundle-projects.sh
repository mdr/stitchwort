#!/usr/bin/env bash
# Copies the AoC project and the roguelike into the playground's bundle
# (docs/proposals/playground-projects.md §5):
#   web/bundle-projects.sh REPO_ROOT OUT_DIR
# writes OUT_DIR/projects/aoc/{manifest.json,src/**/*.sw,examples/YYYY/*.txt,...}
# and OUT_DIR/projects/rogue/{manifest.json,src/**/*.sw}.
# Only aoc/src/**/*.sw, aoc/examples/YYYY/*.txt and aoc/inputs/YYYY/*.txt are
# copied, by those patterns, never the whole aoc/ folder (the puzzle inputs are
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
examples=$(find examples inputs -mindepth 2 -maxdepth 2 -type f -path '*/[0-9][0-9][0-9][0-9]/*.txt' | sort)
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

# One day per src/Aoc/YearYYYY/DayNN/DayNN.sw, newest year first, with its
# tests if the day's folder has Tests/, its proofs if it has Proofs/, and its
# example and puzzle inputs if examples/YYYY/dayNN.txt and
# inputs/YYYY/dayNN.txt exist.
{
  printf '{\n  "name": "aoc",\n  "title": "Advent of Code",\n  "files": ['
  sep=""
  for path in $files; do
    printf '%s\n    "%s"' "$sep" "$path"
    sep=","
  done
  # The files `include` reads (the puzzle inputs and examples): sent to the compiler with
  # the sources, never shown or edited.
  printf '\n  ],\n  "data": ['
  sep=""
  for path in $examples; do
    printf '%s\n    "%s"' "$sep" "$path"
    sep=","
  done
  printf '\n  ],\n  "days": ['
  sep=""
  for year_folder in $(find src/Aoc -mindepth 1 -maxdepth 1 -type d -name 'Year[0-9][0-9][0-9][0-9]' | sort -r); do
    year=${year_folder##*/Year}
    for program in $(find "$year_folder" -mindepth 2 -maxdepth 2 -type f -name 'Day[0-9][0-9].sw' | sort); do
      day=$(basename "$program" .sw)
      n=${day#Day}
      namespace="Aoc.Year$year.$day"
      namespaces="\"$namespace\""
      if [ -d "$year_folder/$day/Tests" ]; then
        namespaces="$namespaces, \"$namespace.Tests\""
      fi
      if [ -d "$year_folder/$day/Proofs" ]; then
        namespaces="$namespaces, \"$namespace.Proofs\""
      fi
      inputs=""
      isep=""
      if [ -f "examples/$year/day$n.txt" ]; then
        inputs="{ \"title\": \"Example\", \"path\": \"examples/$year/day$n.txt\" }"
        isep=", "
      fi
      if [ -f "inputs/$year/day$n.txt" ]; then
        inputs="$inputs$isep{ \"title\": \"Puzzle input\", \"path\": \"inputs/$year/day$n.txt\" }"
      fi
      printf '%s\n    { "title": "Day %d", "year": "%s", "open": "%s", "namespaces": [%s], "main": "%s.main", "inputs": [%s] }' \
        "$sep" "$((10#$n))" "$year" "$program" "$namespaces" "$namespace" "$inputs"
      sep=","
    done
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
