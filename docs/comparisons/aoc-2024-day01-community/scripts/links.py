"""Pull GitHub links out of the megathread's functional and proof comments.

Usage: python3 -I links.py FP_TXT PATHS_TSV REPOS_TXT

FP_TXT is langs.py's fp.txt. A link to a file (github.com/O/R/blob/BRANCH/PATH)
goes to PATHS_TSV as OWNER/REPO <tab> PATH <tab> language <tab> author; a link
to a repository or folder goes to REPOS_TXT as OWNER/REPO <tab> language, for
find.py. One entry per comment author.
"""
import re
import sys

fp, paths_out, repos_out = sys.argv[1:4]
blocks = open(fp).read().split("\n===== ")
seen = set()
paths, repos = [], []
BLOB = re.compile(r"github\.com/([\w.-]+)/([\w.-]+)/blob/[^/\s)\]]+/([^\s)\]#?]+)")
REPO = re.compile(r"github\.com/([\w.-]+)/([\w.-]+)(?:/tree/[^\s)\]]*)?")
for b in blocks:
    head, _, body = b.partition("\n")
    parts = [p.strip() for p in head.strip("= ").split("|")]
    lang, author = parts[0], parts[1]
    if author in seen:
        continue
    body = body.replace("\\", "")
    m = BLOB.search(body)
    if m:
        paths.append(f"{m.group(1)}/{m.group(2)}\t{m.group(3)}\t{lang}\t{author}")
        seen.add(author)
        continue
    m = REPO.search(body)
    if m:
        repos.append(f"{m.group(1)}/{m.group(2)}\t{lang}\t{author}")
        seen.add(author)
open(paths_out, "w").write("\n".join(paths) + "\n")
open(repos_out, "w").write("\n".join(repos) + "\n")
print(len(paths), "file links,", len(repos), "repo links")
