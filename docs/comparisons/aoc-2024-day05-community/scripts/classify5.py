"""Pick one day 5 file per GitHub author and tag its part 2 method by regex.

Usage: python3 -I classify5.py PATHS_TSV FILES_DIR OUT_TSV

PATHS_TSV is find5.py's output (OWNER/REPO, language, path); FILES_DIR holds
fetch5.py's copies. Per owner keeps the largest fetched file that looks like
day 5 (mentions a `|` rule split, or "rule"/"update"/"order"). Tags are
upper bounds: a word can match in code that does something else.
Writes OWNER/REPO, language, path, code lines, tags; prints the tallies.
"""
import collections
import os
import re
import sys

TAGS = {
    "sort with a comparator": r"sortBy|sortWith|sort_by|sort-by|sortWith|mergeSort|qsort|insertionSort|Enum\.sort\(|List\.sort\b|Seq\.sortWith|\.sorted\(|sortInPlaceWith|compareWith|\bsort\b",
    "topological sort": r"(?i)topo|kahn|indegree|in_degree|inDegree",
    "repeated swaps": r"(?i)swap|bubble",
    "predecessor count as key": r"(?i)count.{0,40}(before|precede|rule|deps)|(before|precede|deps).{0,40}(length|count|size)",
    "neighbours-only part 1": r"zip\s*\w*\s*\(?\s*(tail|drop 1|List\.tail|\w+\.tail)|slidingPairs|sliding\(2|chunk_every\(\s*\w*,?\s*2\s*,\s*1|windowed\s*2|pairwise\b|zipWith.{0,30}tail|List\.zip\s*\w+\s*\(List\.tail|partition-all 2 1|window\(2|windows\(2",
    "detects a cycle or checks the order": r"(?i)cycle|cyclic|transitiv|is_total|isTotal|antisymm|not a DAG|no valid order",
}
SRC = re.compile(r"\|")
DAY = re.compile(r"(?i)rule|update|order|page")

paths, files, out = sys.argv[1:4]
best = {}
for line in open(paths):
    repo, lang, path = line.rstrip("\n").split("\t")
    f = os.path.join(files, repo.replace("/", "_") + "__" + path.replace("/", "_"))
    if not os.path.exists(f):
        continue
    text = open(f, errors="replace").read()
    if not (SRC.search(text) and DAY.search(text)):
        continue
    owner = repo.split("/")[0].lower()
    if owner not in best or len(text) > len(best[owner][3]):
        best[owner] = (repo, lang, path, text)

tally = collections.Counter()
bylang = collections.defaultdict(collections.Counter)
with open(out, "w") as w:
    for owner, (repo, lang, path, text) in sorted(best.items()):
        code = [l for l in text.splitlines() if l.strip() and not re.match(r"\s*(--|//|#|;|\(\*|/\*|\*)", l)]
        tags = [k for k, rx in TAGS.items() if re.search(rx, text)]
        tally.update(tags)
        bylang[lang].update(tags + ["files"])
        w.write(f"{repo}\t{lang}\t{path}\t{len(code)}\t{','.join(tags)}\n")
print("authors", len(best))
for k, v in tally.most_common():
    print(f"{v:4}  {k}")
for lang, c in sorted(bylang.items(), key=lambda x: -x[1]["files"]):
    print(f"  {lang:12} files {c['files']:3}  comparator {c['sort with a comparator']:3}  topo {c['topological sort']:3}  "
          f"swaps {c['repeated swaps']:3}  checks {c['detects a cycle or checks the order']:3}")
