"""Check adv5.py's copy of List.sortWith against the real program.

Usage: python3 -I cross5.py STITCHWORT AOC_DIR OUT_DIR N

Writes N random small inputs (pages 1..6, random rules, one update of 3 to 5
pages, the update not already in order) to OUT_DIR, runs
`stitchwort run Aoc.Year2024.Day05.main` on each from AOC_DIR, and compares
its part 2 with the middle page of adv5.py's `p2_stitchwort`. Prints each
mismatch and a tally of the cases' classes.
"""
import importlib.util
import os
import random
import subprocess
import sys
from collections import Counter

sw, aoc, out, n = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
spec = importlib.util.spec_from_file_location("adv5", os.path.join(os.path.dirname(os.path.abspath(__file__)), "adv5.py"))
adv5 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adv5)

os.makedirs(out, exist_ok=True)
rng = random.Random(5)
tally, bad, done = Counter(), 0, 0
while done < n:
    rules = sorted({(a, b) for a in range(1, 7) for b in range(1, 7) if a != b and rng.random() < 0.25})
    if not rules:
        continue
    u = rng.sample(range(1, 7), rng.choice([3, 5]))
    rule = lambda a, b: (a, b) in rules
    if adv5.p1_all_pairs(rule, u):
        continue
    cls, _ = adv5.classify(rule, u)
    expect = adv5.p2_stitchwort(rule, u)[len(u) // 2]
    path = os.path.join(out, f"case{done:03}.txt")
    open(path, "w").write("\n".join(f"{a}|{b}" for a, b in rules) + "\n\n" + ",".join(map(str, u)))
    r = subprocess.run([sw, "run", "Aoc.Year2024.Day05.main"], cwd=aoc, stdin=open(path), capture_output=True, text=True)
    got = [l for l in r.stdout.splitlines() if l.startswith("Part 2")]
    tally[cls] += 1
    if got != [f"Part 2: {expect}"]:
        bad += 1
        print("MISMATCH", path, cls, got, expect, r.stderr[:200])
    done += 1
print("cases", dict(tally), "mismatches", bad)
