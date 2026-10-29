"""Find more AoC 2025 repositories in proof languages with `gh search repos`.

Usage: python3 -I repos9.py KNOWN_REPOS OUT

Searches "advent of code 2025" and "aoc 2025" per language, keeps
repositories not already in KNOWN_REPOS, one OWNER/REPO per line.
"""
import json
import subprocess
import sys
import time

LANGS = ["Lean", "Idris", "Agda", "Dafny", "Coq", "Rocq", "F*", "Isabelle", "Koka", "Roc", "Unison", "Lean 4"]
known = {l.strip() for l in open(sys.argv[1])}
found = []
for lang in LANGS:
    for q in ["advent of code 2025", "aoc 2025", "aoc2025", "advent-of-code-2025"]:
        r = subprocess.run(["gh", "search", "repos", q, "--language", lang, "--limit", "40",
                            "--json", "fullName,pushedAt"], capture_output=True, text=True)
        if r.returncode == 0:
            for h in json.loads(r.stdout):
                if h["fullName"] not in known and h["pushedAt"] >= "2025-12" and h["fullName"] not in found:
                    found.append(h["fullName"])
        time.sleep(3)
    print(lang, len(found), file=sys.stderr)
open(sys.argv[2], "w").write("\n".join(found) + "\n")
