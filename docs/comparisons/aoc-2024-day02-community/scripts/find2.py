"""Find each seed repository's AoC 2024 day 2 source file(s).

Usage: python3 -I find2.py REPOS_TSV OUT_TSV

For each OWNER/REPO (first column), lists the default branch's tree with `gh api` and keeps
paths whose file name or folder looks like day 2 (day02, Day2, 02., day_02, a
folder `2` or `02`), with a source extension, preferring paths that mention
2024. Writes OWNER/REPO <tab> path per hit.
"""
import json
import re
import subprocess
import sys

EXT = re.compile(r"\.(lean|idr|agda|dfy|v|fst|thy|hs|ml|scala|sc|fs|fsx|gleam|ex|exs|clj|cljc|kk|roc|u|elm|am|purs|rkt|scm|lisp|erl|effekt|sw|mo|purs|res)$")
DAY = re.compile(r"(?i)(^|[/_\-.])(day[_\-]?0?2|d0?2|0?2)([/_\-.]|$)|day[_\-]?0?2(?!\d)|(^|/)0?2/")


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
    seeds = [l.split()[0] for l in open(sys.argv[1]) if l.strip()]
    with open(sys.argv[2], "w") as f:
        for repo in seeds:
            paths = [p for p in tree(repo) if EXT.search(p) and DAY.search(p)
                     and not re.search(r"(?i)12|22|test|spec|input", p.rsplit("/", 1)[-1])]
            pref = [p for p in paths if "2024" in p or "24" in p.split("/")[0]]
            hits = pref or paths
            for p in hits[:6]:
                f.write(f"{repo}\t{p}\n")
            print(repo, len(hits), file=sys.stderr)


main()
