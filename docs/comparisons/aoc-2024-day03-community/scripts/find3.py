"""Find each repository's AoC 2024 day 3 source file(s).

Usage: python3 -I find3.py REPOS_TSV OUT_TSV

REPOS_TSV has OWNER/REPO <tab> language lines (from repos3.py). For each,
lists the default branch's tree with `gh api` (saved per repository under
OUT_TSV's folder, trees/, so a rerun after a dropped connection fetches
only what is missing) and keeps paths whose file name or folder looks like
day 3 with a source extension, preferring paths that mention 2024. Writes
OWNER/REPO <tab> language <tab> path, at most three per repository.
"""
import json
import os
import re
import subprocess
import sys

EXT = re.compile(r"\.(lean|idr|agda|dfy|v|fst|thy|hs|ml|scala|sc|fs|fsx|gleam|ex|exs|clj|cljc|kk|roc|u|elm|purs|rkt|scm|lisp|erl|pl|jl)$")
DAY3 = re.compile(r"(?i)(^|[/_\-.])(day[_\-]?0?3|d0?3|0?3)([/_\-.]|$)|day[_\-]?0?3(?!\d)|(^|/)0?3/")
NOT = re.compile(r"(?i)1[3]|2[3]|3[0-9]|test|spec|input|example")


def tree(repo, cache):
    dest = os.path.join(cache, repo.replace("/", "_") + ".json")
    if not os.path.exists(dest):
        try:
            out = subprocess.run(["gh", "api", f"repos/{repo}/git/trees/HEAD?recursive=1"],
                                 capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            return []
        if out.returncode != 0:
            return []
        open(dest, "w").write(out.stdout)
    try:
        data = json.load(open(dest))
    except ValueError:
        return []
    return [t["path"] for t in data.get("tree", []) if t["type"] == "blob"]


def main():
    cache = os.path.join(os.path.dirname(os.path.abspath(sys.argv[2])), "trees")
    os.makedirs(cache, exist_ok=True)
    with open(sys.argv[2], "w") as f:
        for line in open(sys.argv[1]):
            if not line.strip():
                continue
            repo, lang = line.rstrip("\n").split("\t")[:2]
            paths = [p for p in tree(repo, cache)
                     if EXT.search(p) and DAY3.search(p) and not NOT.search(p.rsplit("/", 1)[-1])]
            pref = [p for p in paths if "2024" in p or "24" in p.split("/")[0]]
            hits = [p for p in (pref or paths) if not re.search(r"20(1\d|2[0-35])", p)]
            for p in hits[:3]:
                f.write(f"{repo}\t{lang}\t{p}\n")


main()
