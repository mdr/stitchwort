"""Classify the fetched AoC 2024 day 3 files by method, one per author.

Usage: python3 -I classify3.py FILES_DIR OUT_TSV

Keeps files that mention `mul` (or the character 'm', for a list pattern),
one per author (the owner of the repository; the longest such file, or
the files of a repository that splits day 3 into a parser and a solver,
joined). The language comes from the extension. Method tags are regex
hits, so they are leads to read, not verdicts:
  regex     a regex library or literal
  comb      a parser-combinator library or a hand-made parser monad
  prefix    prefix tests by hand (isPrefixOf, startsWith, stripPrefix, binary or list patterns)
  split     part 2 by splitting on "don't()" / "do()"
  bound     the numbers limited to 1-3 digits somewhere ({1,3}, 3 digits, < 1000, take 3)
  proof     theorem, lemma, ensures, sorry, Refl, decide, #guard, example :=
Writes author, language, tags, code lines (not blank, not comment-only), file.
"""
import collections
import os
import re
import sys

LANG = {"lean": "Lean", "hs": "Haskell", "clj": "Clojure", "scala": "Scala", "sc": "Scala", "ml": "OCaml",
        "ex": "Elixir", "exs": "Elixir", "gleam": "Gleam", "fs": "F#", "fsx": "F#", "roc": "Roc",
        "pl": "Prolog", "lisp": "Common Lisp", "idr": "Idris", "jl": "Julia", "dfy": "Dafny", "agda": "Agda"}
TAGS = {
    "regex": r"Regex|regex|re\.|~r/|~r\"|re-seq|re-find|re-pattern|#\"|Str\.regexp|Re\.|Pcre|\.r\b|\"\"\".*\\\\d|=~|Text\.Regex",
    "comb": r"Parsec|parsec|ReadP|Megaparsec|attoparsec|Angstrom|angstrom|FParsec|nimble_parsec|Parser\b|parser\b|<\|>|\*>|<\*|Std\.Internal\.Parsec|pstring|pchar|many1|sepBy|-->|instaparse|party|nibble",
    "prefix": r"isPrefixOf|stripPrefix|startsWith|starts_with|startswith|String\.starts|<<\"mul\(|\"mul\(\" <> |'m' *:: *'u'|\[\s*'m'\s*,\s*'u'|'m'\s*:\s*'u'|\\\\m\\\\u|drop_prefix|dropPrefix|\"mul\(\" ::|\[\?m, \?u|\bmatch_prefix",
    "split": r"split[^\n]{0,40}don't|splitOn[^\n]{0,20}don't|String\.split\([^\n]{0,30}don't|\"don't\(\)\"[^\n]{0,40}split|breakOn",
    "bound": r"\{1,3\}|<\s*1000|<=\s*999|take\s*3|3 digits|three digits|1-3|maxDigits|\bupTo 3|count' 1 3|between 1 3",
    "part2": r"don'?t|dont|\\bDont\\b|'n'",
    "proof": r"\btheorem\b|\blemma\b|\bensures\b|\bsorry\b|\bRefl\b|\bdecide\b|#guard|^example\b|\bnative_decide\b",
}
COMMENT = re.compile(r"^\s*(--|//|;|#(?!\")|\(\*|%|\*|\|\|\|)")

src = sys.argv[1]
byauthor = collections.defaultdict(list)
for name in sorted(os.listdir(src)):
    text = open(os.path.join(src, name), errors="replace").read()
    if "mul" not in text and "'m'" not in text:
        continue
    owner = name.split("_")[0] if "__" in name else name
    repo = name.split("__")[0]
    byauthor[owner].append((repo, name, text))
rows = []
for owner, files in byauthor.items():
    # Take the repository with the most day-3 text, and all its day-3 files.
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
