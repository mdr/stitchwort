"""List the megathread's inline functional solutions by size, and print some.

Usage: python3 -I inline.py FP_TXT [LANG MAX_SHOWN]

FP_TXT is langs.py's fp.txt. Takes the code of each comment (four-space
indented lines or ``` fences), counts its non-blank lines and how it counts
for part 2 (a map or Counter, `count`/`filter` per left id, or a sorted
merge), and prints one row per comment with code. With LANG, also prints the
code of the MAX_SHOWN shortest comments in that language.
"""
import re
import sys

blocks = open(sys.argv[1]).read().split("\n===== ")
want = sys.argv[2] if len(sys.argv) > 2 else None
shown = int(sys.argv[3]) if len(sys.argv) > 3 else 0
rows = []
for b in blocks:
    head, _, body = b.partition("\n")
    parts = [p.strip() for p in head.strip("= ").split("|")]
    body = body.replace("\\", "")
    code = []
    fence = False
    for line in body.splitlines():
        if line.strip().startswith("```"):
            fence = not fence
            continue
        if fence or line.startswith("    "):
            code.append(line)
    code = [l for l in code if l.strip()]
    if not code:
        continue
    text = "\n".join(code)
    if re.search(r"(?i)counter|frequenc|hashmap|map\.|Map\.|dict|countBy|count_by|frequencies|group_by|groupBy|insertWith|fromListWith|IntMap|tally|multiset", text):
        p2 = "map"
    elif re.search(r"(?i)count|filter|length", text):
        p2 = "count"
    else:
        p2 = "?"
    rows.append((parts[0], len(code), p2, parts[1], text))
rows.sort(key=lambda r: (r[0], r[1]))
for lang, n, p2, author, _ in rows:
    print(f"{lang}\t{n}\t{p2}\t{author}")
if want:
    for lang, n, p2, author, text in [r for r in rows if r[0] == want][:shown]:
        print(f"\n--- {lang} {author} ({n} lines, part 2: {p2})\n{text}")
