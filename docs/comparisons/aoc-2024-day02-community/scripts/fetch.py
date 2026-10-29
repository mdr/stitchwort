"""Fetch solution files from raw.githubusercontent.com.

Usage: python3 -I fetch.py PATHS_TSV OUT_DIR [EXCLUDE_REGEX]

PATHS_TSV has OWNER/REPO <tab> path lines (from find9.py or a search).
Each file is saved as OUT_DIR/OWNER_REPO__path_with_underscores. Lines
matching EXCLUDE_REGEX are skipped. Prints failures.
"""
import os
import re
import sys
import urllib.request

paths, out = sys.argv[1], sys.argv[2]
skip = re.compile(sys.argv[3]) if len(sys.argv) > 3 else None
os.makedirs(out, exist_ok=True)
n = 0
for line in open(paths):
    line = line.rstrip("\n")
    if not line or (skip and skip.search(line)):
        continue
    repo, path = line.split("\t")
    name = repo.replace("/", "_") + "__" + path.replace("/", "_")
    dest = os.path.join(out, name)
    if os.path.exists(dest):
        continue
    url = f"https://raw.githubusercontent.com/{repo}/HEAD/{path}"
    try:
        with urllib.request.urlopen(url, timeout=30) as r:
            data = r.read()
        if len(data) > 400_000:
            print("TOO BIG", repo, path)
            continue
        open(dest, "wb").write(data)
        n += 1
    except Exception as e:  # noqa: BLE001
        print("FAIL", repo, path, e)
print("fetched", n)
