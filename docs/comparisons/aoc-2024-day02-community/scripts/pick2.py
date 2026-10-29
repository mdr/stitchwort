"""Keep one day 2 source file per GitHub author.

Usage: python3 -I pick2.py REPOS_TSV PATHS_TSV OUT_TSV

REPOS_TSV is OWNER/REPO <tab> language (repos2.py); PATHS_TSV is find2.py's
output. Per owner, keeps the first repository's best path: the language's own
extension first, then a file name that says day 2, then the shortest path.
Writes OWNER/REPO <tab> path <tab> language.
"""
import re
import sys

EXT = {"Lean": ["lean"], "Idris": ["idr"], "Agda": ["agda"], "Dafny": ["dfy"], "Coq": ["v"], "Koka": ["kk"],
       "Roc": ["roc"], "Haskell": ["hs"], "OCaml": ["ml"], "Scala": ["scala", "sc"], "F#": ["fs", "fsx"],
       "Gleam": ["gleam"], "Elixir": ["ex", "exs"], "Clojure": ["clj", "cljc"], "Elm": ["elm"],
       "PureScript": ["purs"], "Racket": ["rkt"]}
lang = dict(l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip())
by_repo = {}
for l in open(sys.argv[2]):
    repo, path = l.rstrip("\n").split("\t")
    by_repo.setdefault(repo, []).append(path)
seen_owner = set()
with open(sys.argv[3], "w") as f:
    for repo, paths in by_repo.items():
        owner = repo.split("/")[0].lower()
        exts = EXT.get(lang.get(repo, ""), [])
        good = [p for p in paths if p.rsplit(".", 1)[-1] in exts]
        if owner in seen_owner or not good:
            continue
        good.sort(key=lambda p: (not re.search(r"(?i)day[_\-]?0?2(?!\d)", p.rsplit("/", 1)[-1]), len(p)))
        seen_owner.add(owner)
        f.write(f"{repo}\t{good[0]}\t{lang[repo]}\n")
print(len(seen_owner))
