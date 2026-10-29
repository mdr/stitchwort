"""Fetch the r/adventofcode 2024 Day 2 megathread from the Arctic Shift archive.

Usage: python3 -I arctic.py OUT_DIR

Two requests at most: a post search for the 2 Dec 2024 05:00 UTC window,
then the comment tree of the "Day 2 Solutions" post. Saves posts.json and
tree.json and never re-fetches a saved file. Backs off on HTTP 429. No
requests to reddit.com.
"""
import json
import os
import sys
import time
import urllib.error
import urllib.request

out = sys.argv[1]
base = "https://arctic-shift.photon-reddit.com/api"


def get(url, dest):
    if os.path.exists(dest):
        return json.load(open(dest))
    req = urllib.request.Request(url, headers={"User-Agent": "stitchwort-aoc-note/1 (research, few requests)"})
    for wait in (0, 60, 180, 400):
        time.sleep(wait)
        try:
            with urllib.request.urlopen(req, timeout=180) as r:
                data = r.read()
            break
        except urllib.error.HTTPError as e:
            if e.code != 429:
                raise
            print("429, backing off", file=sys.stderr)
    else:
        sys.exit("gave up after 429s")
    open(dest, "wb").write(data)
    return json.loads(data)


posts = get(f"{base}/posts/search?subreddit=adventofcode&after=2024-12-02T04:50:00&before=2024-12-02T05:20:00&limit=50",
            os.path.join(out, "posts.json"))
cands = [p for p in posts["data"] if "Day 2 Solutions" in p["title"]]
for p in posts["data"]:
    print(p["id"], p["created_utc"], p["title"][:70])
pid = cands[0]["id"]
time.sleep(10)
tree = get(f"{base}/comments/tree?link_id=t3_{pid}&limit=25000", os.path.join(out, "tree.json"))
print("post", pid, "num_comments", cands[0].get("num_comments"), "top-level", len(tree["data"]))
