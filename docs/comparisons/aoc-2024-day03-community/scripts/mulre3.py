"""Classify the `mul` regexes written inline in the Day 3 megathread.

Usage: python3 -I mulre3.py TREE_JSON

Finds, in each live top-level comment, the first line of code that looks
like a regex for `mul(` (it has `mul` followed by an escaped bracket), and
counts how its numbers are matched: `{1,3}`, unbounded (`\\d+`, `[0-9]+`,
`\\d*`), or other; and whether it lets spaces in (`\\s`, ` *`, ` ?`).
Then it runs each regex that Python can compile on a set of edge cases
and counts how many get each one right. Prints counts.
"""
import json
import re
import sys

tree = json.load(open(sys.argv[1]))["data"]
top = [c["data"] if "data" in c and "body" in c.get("data", {}) else c for c in tree]
live = [c for c in top if "body" in c and c["body"] not in ("[deleted]", "[removed]")]

MULRE = re.compile(r"mul\\\\?\(|mul\\\(|mul\[\(\]")
CASES = {  # memory -> the products the puzzle's rule finds
    "mul(1234,5)": [], "mul(12,3456)": [], "mul(123,4)": [492], "mul( 1,2)": [], "mul(1, 2)": [],
    "mul(1,2,3)": [], "mul()": [], "mul(-1,2)": [], "mul(+1,2)": [], "mul(1,2": [],
    "mul(mul(2,3))": [6], "xmul(2,4)%&mul[3,7]": [8],
}
POSITIVE = ["mul(123,4)", "mul(mul(2,3))", "xmul(2,4)%&mul[3,7]"]
regexes = []
for c in live:
    body = c["body"].replace("\\\\", "\\")
    for line in body.splitlines():
        if MULRE.search(line) and ("\\d" in line or "[0-9]" in line):
            regexes.append(line.strip())
            break
bound = sum(1 for r in regexes if "{1,3}" in r)
unb = sum(1 for r in regexes if re.search(r"\\d[+*]|\[0-9\][+*]", r) and "{1,3}" not in r)
spaces = sum(1 for r in regexes if re.search(r"\\s|\s\*|\s\?", r.split("mul", 1)[1][:30]))
print(f"comments with an inline mul regex: {len(regexes)}; {{1,3}}: {bound}; unbounded: {unb}; spaces allowed: {spaces}")

# Run the ones whose quoted pattern Python can compile.
QUOTED = re.compile(r"""r?["'/`](.*?mul.*?)["'/`]""")
ran = right = 0
wrong = {}
for line in regexes:
    m = QUOTED.search(line)
    if not m:
        continue
    pat = m.group(1)
    try:
        rx = re.compile(pat)
    except re.error:
        continue
    if rx.groups < 2:
        continue
    def products(memory):
        got = []
        for mm in rx.finditer(memory):
            try:
                a, b = [g for g in mm.groups() if g is not None][:2]
                got.append(int(a) * int(b))
            except (ValueError, TypeError):
                pass
        return got
    # Skip a pattern this harness misreads (its groups aren't the two numbers):
    # it must get the puzzle's own positive cases right first.
    if any(products(m) != CASES[m] for m in POSITIVE):
        continue
    ran += 1
    ok = True
    for memory, want in CASES.items():
        if products(memory) != want:
            ok = False
            wrong[memory] = wrong.get(memory, 0) + 1
    right += ok
print(f"ran {ran} regexes (those this harness reads right on {POSITIVE}) on {len(CASES)} edge cases: {right} right on all")
for memory, n in sorted(wrong.items(), key=lambda kv: -kv[1]):
    print(f"  wrong on {memory!r}: {n}")
