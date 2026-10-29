"""Classify the fetched AoC 2024 day 4 files by method, one per author.

Usage: python3 -I classify4.py FILES_DIR OUT_TSV

Keeps files that mention XMAS (or the letters as characters, 'X' and 'M'),
one per author (the owner of the repository; the longest such file, or the
files of a repository that splits day 4 into several files, joined). The
language comes from the extension. Method tags are regex hits, so they are
leads to read, not verdicts:
  map       the grid as a map/dictionary keyed by position; a lookup off the grid misses
  array     an array, vector or 2-D array type for the grid
  bounds    explicit bounds tests (0 <=, >= 0, < width, inBounds, in_bounds, isValid)
  safe      an optional lookup (getOrElse, get?, Map.lookup, Enum.at, nth with a default, ...)
  except    an exception caught or rescued for out-of-range reads
  pad       the grid padded with a border
  strings   lines read as strings: transpose, rotate, diagonals, then count substrings
  dirs      a list of the eight directions as offsets
  part2     MAS/SAM or an X-MAS check is present
  proof     theorem, lemma, ensures, sorry, Refl, decide, #guard, example :=
  partial   partial def / decreases * / assert_total (termination not checked)
Writes author, language, tags, code lines (not blank, not comment-only), file.
"""
import collections
import os
import re
import sys

LANG = {"lean": "Lean", "hs": "Haskell", "clj": "Clojure", "scala": "Scala", "sc": "Scala", "ml": "OCaml",
        "ex": "Elixir", "exs": "Elixir", "gleam": "Gleam", "fs": "F#", "fsx": "F#", "roc": "Roc",
        "pl": "Prolog", "lisp": "Common Lisp", "idr": "Idris", "jl": "Julia", "dfy": "Dafny", "agda": "Agda",
        "py": "Python"}
TAGS = {
    "map": r"Map\.fromList|Map\.from_list|Map\.new|Dict\.from_list|dict\.from_list|HashMap|Std\.HashMap|M\.fromList|Map\.of|into \{\}|zipmap|Map\.ofList|Map\.ofSeq|toMap\b|\.to_map|Dict\.insert|dict\.insert|Map\.put",
    "array": r"\bArray\b|Array2D|array2D|\bVector\b|Data\.Array|listArray|UArray|\bVec\b|:array|Array\.make_matrix|Array\.init|Arr\.|\btuple\b|Tuple\.|\bvec\b|mapv|into \[\]",
    "bounds": r"[<>]=\s*0\b|0\s*<=|\binBounds\b|in_bounds|inbounds|InBounds|isValid|is_valid|\bvalid\b|inside|in_grid|inGrid|onGrid|on_grid|within",
    "safe": r"getOrElse|get\?|\[[^\]]*\]\?|Map\.lookup|M\.lookup|Map\.get|Map\.tryFind|tryItem|tryFind|Enum\.at|get-in|\(get |List\.get|Array\.get|\.get\(|!\?|nth_opt|List\.nth_opt|Dict\.get|dict\.get|\.lift\(|Option|Maybe",
    "except": r"\btry\b|\brescue\b|\bcatch\b|Invalid_argument|IndexError|IndexOutOfRange|Not_found",
    "pad": r"\bpad|border|replicate 3|\"\.\.\.\"|\"\.\.\.\.|\bPad",
    "strings": r"transpose|rotate|diagonal|isInfixOf|count_substring|countSubstr|\.count\(\"XMAS|reverse[^\n]{0,30}XMAS|\"SAMX\"|re-seq|Regex|regex",
    "dirs": r"\(-1,\s*-1\)|\[-1,\s*-1\]|\{-1,\s*-1\}|-1, -1|\[-1, 0, 1\]|\[-1,0,1\]|\(-1\)\s*,\s*\(-1\)|\(\s*-1\s*,\s*0\s*\)|\bdirections\b|\bdirs\b|\bDirection\b|neighbo",
    "part2": r"MAS|SAM|'M'[^\n]{0,60}'S'|X-MAS|xmas2|part2|Part2|part_2|partTwo",
    "proof": r"\btheorem\b|\blemma\b|\bensures\b|\bsorry\b|\bRefl\b|\bdecide\b|#guard|^example\b|\bnative_decide\b|\binvariant\b",
    "partial": r"\bpartial def\b|decreases \*|assert_total|\bpartial\b",
}
COMMENT = re.compile(r"^\s*(--|//|;|#(?!\")|\(\*|%|\*|\|\|\|)")

src = sys.argv[1]
byauthor = collections.defaultdict(list)
for name in sorted(os.listdir(src)):
    text = open(os.path.join(src, name), errors="replace").read()
    if "XMAS" not in text.upper() and not ("'X'" in text and "'M'" in text) and "?X" not in text:
        continue
    owner = name.split("_")[0] if "__" in name else name
    repo = name.split("__")[0]
    byauthor[owner].append((repo, name, text))
rows = []
for owner, files in byauthor.items():
    # Take the repository with the most day-4 text, and all its day-4 files.
    repos = collections.defaultdict(list)
    for repo, name, text in files:
        repos[repo].append((name, text))
    repo = max(repos, key=lambda r: sum(len(t) for _, t in repos[r]))
    chosen = repos[repo]
    names = [n for n, _ in chosen if not re.search(r"(?i)main\.lean$", n) or len(chosen) == 1]
    text = "\n".join(t for n, t in chosen if n in names)
    ext = names[0].rsplit(".", 1)[-1]
    tags = [k for k, rx in TAGS.items() if re.search(rx, text, re.M)]
    code = sum(1 for l in text.splitlines() if l.strip() and not COMMENT.match(l))
    rows.append((owner, LANG.get(ext, ext), ",".join(tags), code, ";".join(names)))
rows.sort(key=lambda r: (r[1], r[0].lower()))
with open(sys.argv[2], "w") as f:
    f.write("author\tlanguage\ttags\tcode_lines\tfiles\n")
    for r in rows:
        f.write("\t".join(map(str, r)) + "\n")
langs = collections.Counter(r[1] for r in rows)
print(len(rows), "authors;", dict(langs.most_common()))
for tag in TAGS:
    print(tag, sum(1 for r in rows if tag in r[2].split(",")))
codes = sorted(r[3] for r in rows)
print("median code lines", codes[len(codes) // 2])
