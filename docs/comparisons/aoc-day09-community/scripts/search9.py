"""Search GitHub code for AoC 2025 day 9 solutions in proof and FP languages.

Usage: python3 -I search9.py OUT_TSV

Runs a few `gh search code` queries per file extension (terms from the
puzzle: red tiles, rectangles, a loop of green tiles) and writes
OWNER/REPO <tab> path for each hit whose path looks like day 9.
"""
import json
import re
import subprocess
import sys
import time

EXTS = ["lean", "idr", "agda", "dfy", "v", "fst", "thy", "kk", "roc", "u", "hs", "ml",
        "scala", "fs", "gleam", "ex", "clj", "elm", "effekt", "purs", "rkt", "sml", "mo"]
QUERIES = ["red tiles rectangle", "rectangle area tiles 2025", "green tiles"]
DAY9 = re.compile(r"(?i)day[_\-]?0?9|(^|[/_])0?9[/_.]|d0?9")

hits = set()
for ext in EXTS:
    for q in QUERIES:
        r = subprocess.run(["gh", "search", "code", q, "--extension", ext, "--limit", "50",
                            "--json", "repository,path"], capture_output=True, text=True)
        if r.returncode != 0:
            print("ERR", ext, q, r.stderr.strip()[:120], file=sys.stderr)
            time.sleep(20)
            continue
        for h in json.loads(r.stdout):
            if DAY9.search(h["path"]):
                hits.add((h["repository"]["nameWithOwner"], h["path"]))
        time.sleep(7)  # code search allows about 10 requests a minute
with open(sys.argv[1], "w") as f:
    for repo, path in sorted(hits):
        f.write(f"{repo}\t{path}\n")
print(len(hits))
