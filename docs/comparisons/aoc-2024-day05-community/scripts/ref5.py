"""CPython baseline for timing: both parts the common way (a rule set, the
all-pairs check, sort with cmp_to_key). Usage: python3 -I ref5.py < INPUT"""
import functools
import sys

head, tail = sys.stdin.read().strip().split("\n\n")
rules = {tuple(map(int, l.split("|"))) for l in head.split("\n")}
ups = [list(map(int, l.split(","))) for l in tail.split("\n")]
ok = lambda u: all((u[j], u[i]) not in rules for i in range(len(u)) for j in range(i + 1, len(u)))
cmp = functools.cmp_to_key(lambda a, b: -1 if (a, b) in rules else (1 if (b, a) in rules else 0))
print("Part 1:", sum(u[len(u) // 2] for u in ups if ok(u)))
print("Part 2:", sum(sorted(u, key=cmp)[len(u) // 2] for u in ups if not ok(u)))
