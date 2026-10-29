"""Find AoC 2024 repositories in proof and functional languages with `gh search repos`.

Usage: python3 -I repos2.py OUT_TSV

Searches a few phrasings of "advent of code 2024" per language and writes
OWNER/REPO <tab> language, one line per repository, first hit wins.
Re-running skips nothing: it is cheap (repository search allows 30 a minute).
"""
import json
import subprocess
import sys
import time

LANGS = ["Lean", "Idris", "Agda", "Dafny", "Coq", "Rocq Prover", "F*", "Isabelle", "Koka", "Roc", "Unison",
         "Haskell", "OCaml", "Scala", "F#", "Gleam", "Elixir", "Clojure", "Elm", "PureScript", "Racket"]
QS = ["advent of code 2024", "aoc 2024", "aoc2024", "advent-of-code-2024"]
seen = {}
for lang in LANGS:
    for q in QS:
        r = subprocess.run(["gh", "search", "repos", q, "--language", lang, "--limit", "30",
                            "--json", "fullName,pushedAt"], capture_output=True, text=True)
        if r.returncode != 0:
            print("ERR", lang, q, r.stderr.strip()[:100], file=sys.stderr)
            time.sleep(15)
            continue
        for h in json.loads(r.stdout):
            if h["pushedAt"] >= "2024-12" and h["fullName"] not in seen:
                seen[h["fullName"]] = lang
        time.sleep(2.5)
    print(lang, sum(1 for v in seen.values() if v == lang), file=sys.stderr)
with open(sys.argv[1], "w") as f:
    for repo, lang in seen.items():
        f.write(f"{repo}\t{lang}\n")
print(len(seen))
