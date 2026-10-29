"""Does the ray rule (the Stitchwort spec) agree with a flood fill on the real input?

Usage: python3 -I pocket9.py INPUT

Works on the compressed floor: key columns are each red column, the one
after it, and the one before it (so a one-tile channel between two lines is
kept), the same for rows, with a margin. A compressed cell stands for a block
of tiles that are all on the loop or all off it and all alike under the ray
rule. Flood from outside through cells that are off the loop, moving between
neighbouring cells. Prints the 1-apart pairs, then how many cells the two
rules classify differently, and part 2 by the flood reading.
"""
import sys

pts = [tuple(map(int, l.split(","))) for l in open(sys.argv[1]) if l.strip()]
es = list(zip(pts, pts[1:] + pts[:1]))
xs = sorted(set(p[0] for p in pts))
ys = sorted(set(p[1] for p in pts))
print("columns 1 apart:", [(a, b) for a, b in zip(xs, xs[1:]) if b - a == 1])
print("rows 1 apart:", [(a, b) for a, b in zip(ys, ys[1:]) if b - a == 1])
for p, q in es:
    for a, b in [(a, b) for a, b in zip(xs, xs[1:]) if b - a == 1]:
        if p[0] == q[0] and p[0] in (a, b):
            print("  vertical edge on a 1-apart column:", p, q)
    for a, b in [(a, b) for a, b in zip(ys, ys[1:]) if b - a == 1]:
        if p[1] == q[1] and p[1] in (a, b):
            print("  horizontal edge on a 1-apart row:", p, q)


def keys(vals):
    s = set()
    for v in vals:
        s.update((v - 1, v, v + 1))
    s.update((min(vals) - 2, max(vals) + 2))
    return sorted(s)


cols, rows = keys([p[0] for p in pts]), keys([p[1] for p in pts])


def on_loop(x, y):
    return any(min(p[0], q[0]) <= x <= max(p[0], q[0]) and min(p[1], q[1]) <= y <= max(p[1], q[1]) for p, q in es)


def ray_inside(x, y):
    c = 0
    for p, q in es:
        if p[0] == q[0] and p[0] > x and min(p[1], q[1]) <= y < max(p[1], q[1]):
            c += 1
    return c % 2 == 1


R, C = len(rows), len(cols)
loop = [[on_loop(cols[c], rows[r]) for c in range(C)] for r in range(R)]
seen = [[False] * C for _ in range(R)]
seen[0][0] = True
todo = [(0, 0)]
while todo:
    r, c = todo.pop()
    for rr, cc in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)):
        if 0 <= rr < R and 0 <= cc < C and not seen[rr][cc] and not loop[rr][cc]:
            seen[rr][cc] = True
            todo.append((rr, cc))
diff = [(cols[c], rows[r]) for r in range(R) for c in range(C)
        if not loop[r][c] and ray_inside(cols[c], rows[r]) == seen[r][c]]
print(f"compressed cells {R}x{C}; cells where the ray rule and the flood fill differ: {len(diff)}", diff[:5])
