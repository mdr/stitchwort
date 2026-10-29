"""Find AoC 2024 repositories per language with `gh search repos`.

Usage: python3 -I repos3.py KNOWN_TSV OUT_TSV [LANG,LANG,...]

KNOWN_TSV has OWNER/REPO <tab> language lines already found (the day 1
lane's list, the megathread's links); they are kept, and new hits are added.
Proof languages take up to 40 hits per query, functional ones 12, so the
functional side is a sample. Writes OWNER/REPO <tab> language.
"""
import json
import subprocess
import sys
import time

PROOF = ["Lean", "Idris", "Agda", "Dafny", "Coq", "Rocq", "F*", "Isabelle", "Koka", "Roc", "Unison"]
FP = ["Haskell", "OCaml", "Scala", "F#", "Gleam", "Elixir", "Clojure"]
rows = {}
for line in open(sys.argv[1]):
    if line.strip():
        repo, lang = (line.rstrip("\n").split("\t") + [""])[:2]
        rows.setdefault(repo, lang)
only = sys.argv[3].split(",") if len(sys.argv) > 3 else PROOF + FP  # retry a few after a rate limit
for lang in only:
    limit = "40" if lang in PROOF else "12"
    for q in ["advent of code 2024", "aoc 2024", "aoc2024"]:
        r = subprocess.run(["gh", "search", "repos", q, "--language", lang, "--limit", limit,
                            "--sort", "stars", "--json", "fullName,pushedAt"],
                           capture_output=True, text=True)
        if r.returncode == 0:
            for h in json.loads(r.stdout):
                if h["pushedAt"] >= "2024-12":
                    rows.setdefault(h["fullName"], lang)
        else:
            print("ERR", lang, q, r.stderr.strip()[:100], file=sys.stderr)
        time.sleep(7)  # search allows 30 requests a minute, shared with other lanes
    print(lang, len(rows), file=sys.stderr)
with open(sys.argv[2], "w") as f:
    for repo, lang in sorted(rows.items()):
        f.write(f"{repo}\t{lang}\n")
