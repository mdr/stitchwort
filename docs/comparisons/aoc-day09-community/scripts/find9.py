"""Find each seed repository's AoC 2025 day 9 source file(s).

Usage: python3 -I find9.py SEED_REPOS OUT_TSV

For each OWNER/REPO, lists the default branch's tree with `gh api` and keeps
paths whose file name or folder looks like day 9 (day09, Day9, 09., day_09, a
folder `9` or `09`), with a source extension, preferring paths that mention
2025. Writes OWNER/REPO <tab> path per hit.
"""
import json
import re
import subprocess
import sys

EXT = re.compile(r"\.(lean|idr|agda|dfy|v|fst|thy|hs|ml|scala|sc|fs|fsx|gleam|ex|exs|clj|cljc|kk|roc|u|elm|am|purs|rkt|scm|lisp|erl|effekt|sw|mo|jl|rs|py)$")
DAY9 = re.compile(r"(?i)(^|[/_\-.])(day[_\-]?0?9|d0?9|0?9)([/_\-.]|$)|day[_\-]?0?9|(^|/)0?9/")


def tree(repo):
    try:
        out = subprocess.run(
            ["gh", "api", f"repos/{repo}/git/trees/HEAD?recursive=1"],
            capture_output=True, text=True, timeout=60)
    except subprocess.TimeoutExpired:
        return []
    if out.returncode != 0:
        return []
    return [t["path"] for t in json.loads(out.stdout).get("tree", []) if t["type"] == "blob"]


def main():
    seeds = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    with open(sys.argv[2], "w") as f:
        for repo in seeds:
            paths = [p for p in tree(repo) if EXT.search(p) and DAY9.search(p)
                     and not re.search(r"(?i)19|29|test|spec|input", p.rsplit("/", 1)[-1])]
            pref = [p for p in paths if "2025" in p or "25" in p.split("/")[0]]
            hits = pref or paths
            for p in hits[:6]:
                f.write(f"{repo}\t{p}\n")
            print(repo, len(hits), file=sys.stderr)


main()
