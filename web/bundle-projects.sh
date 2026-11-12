#!/usr/bin/env bash
# Copies the AoC project and the roguelike into the playground's bundle
# (docs/proposals/playground-projects.md §5):
#   web/bundle-projects.sh REPO_ROOT OUT_DIR
# writes OUT_DIR/projects/aoc/{manifest.json,src/**/*.sw,examples/YYYY/*.txt,...}
# and OUT_DIR/projects/rogue/{manifest.json,src/**/*.sw}, and likewise for the
# Software Foundations port (sf/, OUT_DIR/projects/sf) and the book (book/,
# OUT_DIR/projects/book, skipped when the folder doesn't exist).
# Only aoc/src/**/*.sw, aoc/examples/YYYY/*.txt and aoc/inputs/YYYY/*.txt are
# copied, by those patterns, never the whole aoc/ folder (the puzzle inputs are
# bundled too). The roguelike, sf/ and book/ get only their src/**/*.sw. The
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

# The playground reads only the .sw files, and shows an open goal (`?`) as a
# goal, not an error, in every project: that is what `check: open-goals: warn`
# asks of `stitchwort check`. So the one setting the config may have besides
# `sources: [src]` is that one; prints the setting (`warn`, or `fail` when the
# config doesn't say).
open_goals_of() {
  local text
  text="$(cat "$1/stitchwort.yaml")"
  if [ "$text" = "sources: [src]" ]; then
    echo fail
  elif [ "$text" = "$(printf 'sources: [src]\ncheck:\n  open-goals: warn')" ]; then
    echo warn
  else
    echo "bundle-projects: $1/stitchwort.yaml must be 'sources: [src]', optionally with 'check:' and '  open-goals: warn' under it" >&2
    exit 1
  fi
}

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

# ---- Chapter projects: sf/ (the Software Foundations port) and book/. ---------
# Their entries are chapters, not days: each opens the chapter's first file and
# checks its namespaces (every `namespace` its files declare) and what they use.
# `slug` is the chapter's part of its link (`#sf/basics`, `#book/3`). A chapter
# has no `main`, so `"noRun": true` tells the page not to offer Run: it would
# only report E-NO-MAIN, while the tests and the open goals are the work.

# json_string_list ITEM...: `"a", "b"`.
json_list() {
  local out="" sep=""
  for item in "$@"; do
    out="$out$sep\"$item\""
    sep=", "
  done
  printf '%s' "$out"
}

# chapter_entry TITLE SLUG OPEN FILE...: one manifest entry; OPEN is the file
# the chapter opens at and FILE... are all its files.
chapter_entry() {
  local title=$1 slug=$2 open=$3
  shift 3
  local namespaces
  namespaces=$(cat "$@" | sed -n 's/^namespace \([A-Za-z0-9_.]*\).*/\1/p' | sort -u)
  # shellcheck disable=SC2086
  printf '{ "title": "%s", "slug": "%s", "open": "%s", "namespaces": [%s], "hint": "This project has no program to run: the Check tab shows what is proved and which goals (the ?s) are still open." }' \
    "$title" "$slug" "$open" "$(json_list $namespaces)"
}

# bundle_chapters NAME TITLE FOLDER ENTRIES_FUNCTION: copies FOLDER's sources
# and writes the manifest; ENTRIES_FUNCTION prints the chapter entries, one per
# line, run inside FOLDER.
bundle_chapters() {
  local name=$1 title=$2 folder=$3 entries=$4
  local out
  out="$(dirname "$dest")/$name"
  if [ ! -f "$root/$folder/stitchwort.yaml" ]; then
    rm -rf "$out"
    return 0
  fi
  local open_goals
  open_goals=$(open_goals_of "$root/$folder")
  cd "$root/$folder"
  local chapter_files path
  chapter_files=$(find src -type f -name '*.sw' | sort)
  for path in $chapter_files; do
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
  rm -rf "$out"
  mkdir -p "$out"
  for path in $chapter_files; do
    mkdir -p "$out/$(dirname "$path")"
    cp "$path" "$out/$path"
  done
  {
    printf '{\n  "name": "%s",\n  "title": "%s",\n  "noRun": true,\n  "openGoals": "%s",\n  "files": [' "$name" "$title" "$open_goals"
    local sep=""
    for path in $chapter_files; do
      printf '%s\n    "%s"' "$sep" "$path"
      sep=","
    done
    printf '\n  ],\n  "data": [],\n  "days": [\n'
    sep=""
    while IFS= read -r entry; do
      printf '%s    %s' "$sep" "$entry"
      sep=$',\n'
    done < <("$entries")
    printf '\n  ]\n}\n'
  } >"$out/manifest.json"
  echo "bundled $folder into $out"
}

# sf/README.md's table, in book order: the folder under src/Sf/Lf/ holds the
# chapter's files, and the chapter opens at the file named like it. Basics also
# gets Nat.sw, the numbers every chapter uses.
sf_entries() {
  local chapter folder open files
  for chapter in Basics Induction Lists Poly; do
    folder="src/Sf/Lf/$chapter"
    open="$folder/$chapter.sw"
    # Lists opens at NatList.sw, where most of the chapter is (sf/README.md).
    [ "$chapter" = "Lists" ] && open="$folder/NatList.sw"
    files=$(find "$folder" -type f -name '*.sw' | sort)
    # shellcheck disable=SC2086
    chapter_entry "$chapter" "$(printf '%s' "$chapter" | tr 'A-Z' 'a-z')" "$open" $files
    echo
  done
}

# book/src/NN-name.sw: a chapter is one file, in order of NN. The title is
# "Chapter N: Title", from the file's `-- Chapter N. Title` header line (just
# "Chapter N" if it has none), and the slug is N.
book_entries() {
  local file base number heading title
  for file in $(find src -mindepth 1 -maxdepth 1 -type f -name '[0-9][0-9]-*.sw' | sort); do
    base=$(basename "$file")
    number=$((10#${base%%-*}))
    heading=$(sed -n 's/^-- Chapter [0-9][0-9]*\. *//p' "$file" | head -n 1)
    title="Chapter $number"
    [ -n "$heading" ] && title="$title: $heading"
    chapter_entry "$title" "$number" "$file" "$file"
    echo
  done
}

bundle_chapters sf "Software Foundations (port)" sf sf_entries
bundle_chapters book "Proving with Stitchwort" book book_entries
