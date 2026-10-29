"""Find AoC 2024 repositories per language with `gh search repos`.

Usage: python3 -I repos.py OUT_TSV [LANG ...]

Searches a few "advent of code 2024" spellings per language and writes
OWNER/REPO <tab> language for repositories pushed since December 2024.
Skips languages already in OUT_TSV, so it can be re-run after a network drop.
"""
import json
import os
import subprocess
import sys
import time

PROOF = ["Lean", "Idris", "Agda", "Dafny", "Coq", "Rocq Prover", "F*", "Isabelle", "Koka", "Roc", "Unison"]
FP = ["Haskell", "OCaml", "Scala", "F#", "Gleam", "Elixir", "Clojure"]
out = sys.argv[1]
langs = sys.argv[2:] or PROOF + FP
done = {}
if os.path.exists(out):
    for line in open(out):
        repo, lang = line.rstrip("\n").split("\t")
        done.setdefault(lang, set()).add(repo)
with open(out, "a") as f:
    for lang in langs:
        if lang in done:
            continue
        found = set()
        for q in ["advent of code 2024", "aoc 2024", "aoc2024", "advent-of-code-2024"]:
            r = subprocess.run(["gh", "search", "repos", q, "--language", lang, "--limit", "50",
                                "--json", "fullName,pushedAt"], capture_output=True, text=True)
            if r.returncode == 0:
                for h in json.loads(r.stdout):
                    if h["pushedAt"] >= "2024-12":
                        found.add(h["fullName"])
            else:
                print("ERR", lang, q, r.stderr.strip()[:100], file=sys.stderr)
            time.sleep(3)
        for repo in sorted(found):
            f.write(f"{repo}\t{lang}\n")
        f.flush()
        print(lang, len(found), file=sys.stderr)
