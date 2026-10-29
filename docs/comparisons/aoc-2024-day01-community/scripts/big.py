"""Write a synthetic day 1 input of N lines, and time a Python reference.

Usage: python3 -I big.py N OUT          (write the input)
       python3 -I big.py ref INPUT      (solve INPUT in Python, print time)

The ids are five-digit numbers drawn from 10,000..99,999 like the real input,
with a seeded generator, so the files are the same each time. The reference
is the usual community solution: sorted/zip for part 1, Counter for part 2.
"""
import random
import sys
import time
from collections import Counter

if sys.argv[1] == "ref":
    t = time.monotonic()
    nums = list(map(int, open(sys.argv[2]).read().split()))
    left, right = sorted(nums[0::2]), sorted(nums[1::2])
    p1 = sum(abs(a - b) for a, b in zip(left, right))
    c = Counter(right)
    p2 = sum(x * c[x] for x in left)
    print(f"{time.monotonic() - t:.3f}s in Python's own clock :: {p1} {p2}")
else:
    n, out = int(sys.argv[1]), sys.argv[2]
    rng = random.Random(1)
    with open(out, "w") as f:
        for _ in range(n):
            f.write(f"{rng.randint(10000, 99999)}   {rng.randint(10000, 99999)}\n")
