"""Make day 2 inputs with long reports, where brute force and linear part 2s differ.

Usage: python3 -I gen2.py LEVELS REPORTS SEED > OUT

Each report rises (or falls) gently for LEVELS levels; a third get one bad
level inserted (so the dampener saves them), a third get two (so it doesn't).
Also prints the expected part 2 answer, by the linear method, to stderr.
"""
import random
import sys

n, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)


def gentle(levels, up):
    return all(1 <= (b - a if up else a - b) <= 3 for a, b in zip(levels, levels[1:]))


def tolerates(levels, up):
    for i, (a, b) in enumerate(zip(levels, levels[1:])):
        if not 1 <= (b - a if up else a - b) <= 3:
            return gentle(levels[:i] + levels[i + 1:], up) or gentle(levels[:i + 1] + levels[i + 2:], up)
    return True


safe = 0
for r in range(count):
    up = rng.random() < 0.5
    x = 10 if up else 10 + 3 * n
    levels = []
    for _ in range(n):
        levels.append(x)
        x += rng.randint(1, 3) if up else -rng.randint(1, 3)
    for _ in range(r % 3):
        k = rng.randrange(1, n - 1)
        levels.insert(k, levels[k] + 50)
    safe += tolerates(levels, True) or tolerates(levels, False)
    print(" ".join(map(str, levels)))
print("part 2:", safe, file=sys.stderr)
