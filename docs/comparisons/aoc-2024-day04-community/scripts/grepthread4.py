"""Print short excerpts of live megathread comments (top level and replies) matching a regex.

Usage: python3 -I grepthread4.py TREE_JSON REGEX [WIDTH]

Walks the whole Arctic Shift comment tree and prints author, language tag
(if any) and WIDTH characters around each comment's first match.
"""
import json
import re
import sys

tree = json.load(open(sys.argv[1]))["data"]
rx = re.compile(sys.argv[2], re.I)
width = int(sys.argv[3]) if len(sys.argv) > 3 else 160


def walk(nodes):
    for n in nodes:
        d = n.get("data", n)
        if "body" in d:
            yield d
        kids = d.get("replies") or n.get("children") or []
        if isinstance(kids, dict):
            kids = kids.get("data", {}).get("children", [])
        yield from walk(kids)


seen = 0
for c in walk(tree):
    b = c["body"]
    if b in ("[deleted]", "[removed]"):
        continue
    m = rx.search(b)
    if not m:
        continue
    seen += 1
    tag = re.search(r"\[\s*language\s*:\s*([^\]]+)\]", b.replace("\\", ""), re.I)
    s = max(0, m.start() - width // 2)
    text = b[s:s + width].replace("\n", " ")
    print(f"- {c.get('author')} [{tag.group(1).strip() if tag else '?'}] {c.get('id')}: …{text}…")
print("matches", seen)
