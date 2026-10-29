"""Fetch solution files from raw.githubusercontent.com.

Usage: python3 -I fetch3.py PATHS_TSV OUT_DIR

PATHS_TSV has OWNER/REPO <tab> [language <tab>] path lines (from find5.py).
Each file is saved as OUT_DIR/OWNER_REPO__path_with_underscores; files
already there are not fetched again. Prints failures.
"""
import os
import sys
import urllib.parse
import urllib.request

paths, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
n = 0
for line in open(paths):
    line = line.rstrip("\n")
    if not line:
        continue
    cols = line.split("\t")
    repo, path = cols[0], cols[-1]
    dest = os.path.join(out, repo.replace("/", "_") + "__" + path.replace("/", "_"))
    if os.path.exists(dest):
        continue
    url = f"https://raw.githubusercontent.com/{repo}/HEAD/{urllib.parse.quote(path)}"
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
