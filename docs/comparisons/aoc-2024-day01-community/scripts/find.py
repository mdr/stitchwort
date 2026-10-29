"""Find each repository's AoC 2024 day 1 source file(s).

Usage: python3 -I find.py REPOS_TSV OUT_TSV

REPOS_TSV has OWNER/REPO <tab> language lines. For each, lists the default
branch's tree with `gh api` (one request) and keeps source files whose name or
folder looks like day 1 (Day01, day_1, 01.lean, a folder `1` or `01`, ...),
preferring paths that mention 2024. Writes OWNER/REPO <tab> path <tab>
language. Skips repositories already in OUT_TSV, so it can resume.
"""
import json
import os
import re
import subprocess
import sys

EXT = re.compile(r"\.(lean|idr|agda|lagda\.md|dfy|v|fst|thy|kk|roc|u|hs|ml|scala|sc|fs|fsx|gleam|ex|exs|clj|cljc|sw)$")
DAY1 = re.compile(r"(?i)(^|[/_\-.])(day[_\-]?0?1|d0?1|p0?1|0?1)(?!\d)([/_\-.a-z]|$)")
BAD = re.compile(r"(?i)test|spec|input|example|lakefile|20(1|2[0-3])\b|/20(1\d|2[0-3])/")

repos_in, out = sys.argv[1], sys.argv[2]
done = set()
if os.path.exists(out):
    done = {l.split("\t")[0] for l in open(out)}
with open(out, "a") as f:
    for line in open(repos_in):
        if not line.strip():
            continue
        repo, lang = line.rstrip("\n").split("\t")[:2]
        if repo in done:
            continue
        done.add(repo)
        try:
            r = subprocess.run(["gh", "api", f"repos/{repo}/git/trees/HEAD?recursive=1"],
                               capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            print("TIMEOUT", repo, file=sys.stderr)
            continue
        if r.returncode != 0:
            f.write(f"{repo}\t-\t{lang}\n")
            continue
        paths = [t["path"] for t in json.loads(r.stdout).get("tree", []) if t["type"] == "blob"]
        paths = [p for p in paths if EXT.search(p) and DAY1.search(p) and not BAD.search(p)]
        pref = [p for p in paths if "2024" in p or "24" in p.split("/")[0]]
        hits = (pref or paths)[:4]
        for p in hits or ["-"]:
            f.write(f"{repo}\t{p}\t{lang}\n")
        f.flush()
        print(repo, len(hits), file=sys.stderr)
