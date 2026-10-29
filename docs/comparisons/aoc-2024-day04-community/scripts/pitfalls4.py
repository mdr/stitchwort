"""Day 4's common pitfalls, run on a real input: which change the answers?

Usage: python3 -I pitfalls4.py INPUT

Prints the right answers (every position and direction, with bounds
checks), then each pitfall's answer:
  wrap        Python indexing with no lower bound check: grid[-1] is the last row
  regex       one non-overlapping regex XMAS|SAMX per line (misses XMASAMX's second word)
  corners     part 2 as "two M and two S among the corners" (takes MAM / SAS)
  plus        part 2 also counting + shapes
  skipmas     part 2 by scanning each diagonal for MAS and resuming after the S
              (amesgen's Lean filterMas), so MASAM loses its second centre
  timing      the right answers' time in-process, ms
"""
import re
import sys
import time

grid = [l for l in open(sys.argv[1]).read().split("\n") if l]
H, W = len(grid), len(grid[0])
D8 = [(dr, dc) for dr in (-1, 0, 1) for dc in (-1, 0, 1) if (dr, dc) != (0, 0)]


def at(r, c):
    return grid[r][c] if 0 <= r < H and 0 <= c < W else None


def part1():
    return sum(all(at(r + i * dr, c + i * dc) == ch for i, ch in enumerate("XMAS"))
               for r in range(H) for c in range(W) for dr, dc in D8)


def mas(a, b):
    return {a, b} == {"M", "S"}


def part2():
    return sum(at(r, c) == "A" and mas(at(r - 1, c - 1), at(r + 1, c + 1)) and mas(at(r - 1, c + 1), at(r + 1, c - 1))
               for r in range(H) for c in range(W))


def part1_wrap():
    n = 0
    for r in range(H):
        for c in range(W):
            for dr, dc in D8:
                try:
                    n += all(grid[r + i * dr][c + i * dc] == ch for i, ch in enumerate("XMAS"))
                except IndexError:
                    pass
    return n


def lines_all():
    rows = grid
    cols = ["".join(grid[r][c] for r in range(H)) for c in range(W)]
    d1 = ["".join(grid[r][r - k] for r in range(H) if 0 <= r - k < W) for k in range(-W, H)]
    d2 = ["".join(grid[r][k - r] for r in range(H) if 0 <= k - r < W) for k in range(H + W)]
    return rows + cols + d1 + d2


def part1_regex():
    return sum(len(re.findall("XMAS|SAMX", l)) for l in lines_all())


def part1_lookahead():
    return sum(len(re.findall("(?=XMAS|SAMX)", l)) for l in lines_all())


def part2_corners():
    n = 0
    for r in range(1, H - 1):
        for c in range(1, W - 1):
            cs = [grid[r - 1][c - 1], grid[r - 1][c + 1], grid[r + 1][c - 1], grid[r + 1][c + 1]]
            n += grid[r][c] == "A" and cs.count("M") == 2 and cs.count("S") == 2
    return n


def part2_plus():
    plus = sum(at(r, c) == "A" and mas(at(r - 1, c), at(r + 1, c)) and mas(at(r, c - 1), at(r, c + 1))
               for r in range(H) for c in range(W))
    return part2() + plus


def part2_skipmas():
    # diagonals as lists of (position, letter), both ways round, scanning MAS and resuming after the S
    def diags(sign):
        out = []
        for k in range(-W - H, W + H):
            d = [((r, c), grid[r][c]) for r in range(H) for c in [sign * (r - k) if sign > 0 else k - r] if 0 <= c < W]
            if d:
                out += [d, d[::-1]]
        return out

    def centres(d):
        found, i = set(), 0
        while i + 2 < len(d):
            if (d[i][1], d[i + 1][1], d[i + 2][1]) == ("M", "A", "S"):
                found.add(d[i + 1][0])
                i += 3
            else:
                i += 1
        return found

    a = set().union(*map(centres, diags(1)))
    b = set().union(*map(centres, diags(-1)))
    return len(a & b)


t = time.perf_counter()
p1, p2 = part1(), part2()
ms = (time.perf_counter() - t) * 1000
print("right", p1, p2)
print("wrap (part 1)", part1_wrap())
print("regex non-overlapping (part 1)", part1_regex(), "lookahead", part1_lookahead())
print("corners 2M2S (part 2)", part2_corners())
print("plus shapes too (part 2)", part2_plus())
print("skip after MAS (part 2)", part2_skipmas())
print(f"timing {ms:.1f} ms")
