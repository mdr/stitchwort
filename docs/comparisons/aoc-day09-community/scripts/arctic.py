"""Fetch the r/adventofcode 2025 Day 9 megathread from the Arctic Shift archive.

Usage: python3 -I arctic.py OUT_DIR

Two requests: a post search for the 9 Dec 2025 05:00 UTC window, then the
comment tree of the "Day 9 Solutions" post. Saves posts.json and tree.json.
No requests to reddit.com.
"""
import json
import os
import sys
import urllib.request

out = sys.argv[1]
base = "https://arctic-shift.photon-reddit.com/api"


def get(url, dest):
    if os.path.exists(dest):
        return json.load(open(dest))
    req = urllib.request.Request(url, headers={"User-Agent": "stitchwort-aoc-note/1 (research, few requests)"})
    with urllib.request.urlopen(req, timeout=120) as r:
        data = r.read()
    open(dest, "wb").write(data)
    return json.loads(data)


posts = get(f"{base}/posts/search?subreddit=adventofcode&after=2025-12-09T04:50:00&before=2025-12-09T05:20:00&limit=50",
            os.path.join(out, "posts.json"))
cands = [p for p in posts["data"] if "Day 9 Solutions" in p["title"]]
for p in posts["data"]:
    print(p["id"], p["created_utc"], p["title"][:70])
pid = cands[0]["id"]
tree = get(f"{base}/comments/tree?link_id=t3_{pid}&limit=25000", os.path.join(out, "tree.json"))
print("post", pid, "num_comments", cands[0].get("num_comments"), "top-level", len(tree["data"]))
