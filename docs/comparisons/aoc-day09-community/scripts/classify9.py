"""Classify fetched day 9 solutions: lines, method markers, proof markers.

Usage: python3 -I classify9.py FILES_DIR > table.tsv

"Lines" counts non-blank lines that don't start with a comment marker (as in
the earlier notes). Method columns are regex hits, a first sort to be checked
by reading; they are not conclusions.
"""
import os
import re
import sys

COMMENT = re.compile(r"^\s*(--|//|#|;|\(\*|\*|\{-|/\*|%)")
MARK = {
    "compress": r"(?i)compress|dedup.*sort|sort.*(nub|dedup|distinct|uniq)|index(Of|Map)|zipWith.*\[0\.\.|M\.fromList.*zip",
    "flood": r"(?i)flood|bfs|dfs",
    "ray": r"(?i)ray|crossing|winding|odd|parity|even",
    "prefix": r"(?i)prefix|summed|cumul|scanl.*scanl|psum|integral",
    "edgecut": r"(?i)intersect|overlap|crosses|cuts|aabb",
    "sortarea": r"(?i)sortOn.*(Down|negate|-)|sortBy.*flip|sortWith.*-|reverse.*sort|sort.*desc|sortDescending|Down",
    "parallel": r"(?i)parallel|par\b|\.par|Task\.|async|pmap",
    "geomlib": r"(?i)shapely|geo\b|polygon(lib)?\.contains|jts",
}
PROOF = {
    "theorem": r"^\s*(theorem|lemma|Lemma|Theorem)\b",
    "ensures": r"\bensures\b",
    "invariant": r"\binvariant\b",
    "sorry": r"\bsorry\b|\badmit\b|Admitted",
    "partial": r"\bpartial\b|TERMINATING|decreases \*|assert_total|believe_me",
    "decide": r"\bdecide\b|native_decide|#eval|#guard|#assert",
}

for name in sorted(os.listdir(sys.argv[1])):
    text = open(os.path.join(sys.argv[1], name), errors="replace").read()
    lines = [l for l in text.splitlines() if l.strip() and not COMMENT.match(l)]
    marks = [k for k, rx in MARK.items() if re.search(rx, text)]
    proofs = [f"{k}:{len(re.findall(rx, text, re.M))}" for k, rx in PROOF.items() if re.search(rx, text, re.M)]
    print(f"{name}\t{len(lines)}\t{','.join(marks)}\t{','.join(proofs)}")
