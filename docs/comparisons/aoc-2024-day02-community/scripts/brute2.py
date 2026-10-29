"""Day 2 by brute force in CPython, for a speed reference.

Usage: python3 -I brute2.py INPUT
"""
import sys

reports = [list(map(int, line.split())) for line in open(sys.argv[1]) if line.strip()]


def ok(a, b):
    return 1 <= b - a <= 3


def safe(xs):
    return all(ok(a, b) for a, b in zip(xs, xs[1:])) or all(ok(b, a) for a, b in zip(xs, xs[1:]))


print(sum(map(safe, reports)), sum(safe(xs) or any(safe(xs[:i] + xs[i + 1:]) for i in range(len(xs))) for xs in reports))
