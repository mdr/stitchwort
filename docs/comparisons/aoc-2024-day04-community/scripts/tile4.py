"""Tile a grid K times across and K times down, for timing on a bigger grid.

Usage: python3 -I tile4.py INPUT K OUTPUT
"""
import sys

rows = [l for l in open(sys.argv[1]).read().split("\n") if l]
k = int(sys.argv[2])
with open(sys.argv[3], "w") as f:
    for _ in range(k):
        for r in rows:
            f.write(r * k + "\n")
