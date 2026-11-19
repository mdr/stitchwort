#!/usr/bin/env python3
"""Adds a blank line before about a third of the lines after each case's first (SW-4153).

Usage: blankify.py IN.cases OUT.cases SEED
"""
import random, sys
src, out, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
r = random.Random(seed)
cases = open(src).read().split('###\n')
res = []
for c in cases:
    if not c.strip():
        continue
    lines = c.split('\n')
    new = [lines[0]]
    for line in lines[1:]:
        if line.strip() and r.random() < 0.35:
            new.append('')
        new.append(line)
    res.append('\n'.join(new))
open(out, 'w').write(''.join(c + '###\n' for c in res))
