"""Summarise classify.tsv: code lines per language, the shortest files, tag counts per language.

Usage: python3 -I stats4.py CLASSIFY_TSV
"""
import collections
import sys

rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
by = collections.defaultdict(list)
for r in rows:
    by[r[1]].append(int(r[3]))
for lang, ns in sorted(by.items(), key=lambda kv: -len(kv[1])):
    ns.sort()
    print(f"{lang:12} n={len(ns):3} min={ns[0]:4} median={ns[(len(ns) - 1) // 2]:4}")
print("shortest:")
for r in sorted(rows, key=lambda r: int(r[3]))[:20]:
    print(f"  {r[3]:>4} {r[1]:10} {r[0]:22} {r[2]}")
tags = sorted({t for r in rows for t in r[2].split(",") if t})
print("tag".ljust(12), " ".join(t[:6].rjust(6) for t in tags))
for lang in sorted(by, key=lambda l: -len(by[l])):
    rs = [r for r in rows if r[1] == lang]
    print(lang[:12].ljust(12), " ".join(str(sum(t in r[2].split(",") for r in rs)).rjust(6) for t in tags))
