"""Day 9 part 2: compare the community's checks with a flood-fill ground truth.

Usage: python3 -I methods9.py INPUT [TRIALS] [SEED]

1. Input facts: point count, coordinate range, distinct columns/rows,
   whether any two distinct red columns (rows) are exactly 1 apart, and the
   longest edges (the "notch").
2. Part 2 on INPUT by three checks, with timings:
   EDGE    reject a rectangle if a loop edge passes through its open interior
           (NerdyPepper's `away` test), accept otherwise;
   EDGE+IN EDGE, plus the rectangle's centre is inside by a ray cast;
   COMPRESS key columns/rows (each red one and the one after), outside
           cells by ray parity, a summed-area table: the Stitchwort method.
3. On TRIALS random small rectilinear loops, the answer of each check against
   a flood fill from outside on the real tile grid (no compression, no ray
   rule): the tiles the fill can't reach are red or green. Prints counts of
   disagreement and the smallest counterexample for each check.
"""
import random
import sys
import time


def parse(path):
    return [tuple(map(int, l.split(","))) for l in open(path) if l.strip()]


def edges(pts):
    return list(zip(pts, pts[1:] + pts[:1]))


def area(a, b):
    return (abs(a[0] - b[0]) + 1) * (abs(a[1] - b[1]) + 1)


def edge_ok(a, b, es):
    x0, x1 = sorted((a[0], b[0]))
    y0, y1 = sorted((a[1], b[1]))
    for (p, q) in es:
        lx0, lx1 = sorted((p[0], q[0]))
        ly0, ly1 = sorted((p[1], q[1]))
        if not (lx1 <= x0 or lx0 >= x1 or ly1 <= y0 or ly0 >= y1):
            return False
    return True


def inside_point(px, py, es):
    """Ray to the right from a point with half-integer-safe coordinates."""
    c = 0
    for (p, q) in es:
        if p[0] == q[0] and p[0] > px:
            lo, hi = sorted((p[1], q[1]))
            if lo <= py < hi:
                c += 1
    return c % 2 == 1


def edge_in_ok(a, b, es):
    if not edge_ok(a, b, es):
        return False
    cx = (a[0] + b[0]) / 2
    cy = (a[1] + b[1]) / 2 + 0.25  # off the rows of horizontal edges
    on = any(min(p[0], q[0]) <= cx <= max(p[0], q[0]) and min(p[1], q[1]) <= cy <= max(p[1], q[1]) for p, q in es)
    return on or inside_point(cx, cy, es)


def on_loop(t, es):
    return any(min(p[0], q[0]) <= t[0] <= max(p[0], q[0]) and min(p[1], q[1]) <= t[1] <= max(p[1], q[1]) for p, q in es)


def red_or_green_ray(t, es):
    return on_loop(t, es) or inside_point(t[0], t[1], es)


def compress_answer(pts):
    es = edges(pts)
    cols = sorted(set([p[0] for p in pts] + [p[0] + 1 for p in pts]))
    rows = sorted(set([p[1] for p in pts] + [p[1] + 1 for p in pts]))
    ci = {v: i for i, v in enumerate(cols)}
    ri = {v: i for i, v in enumerate(rows)}
    R, C = len(rows), len(cols)
    S = [[0] * (C + 1) for _ in range(R + 1)]
    for r in range(R):
        near = [e for e in es if min(e[0][1], e[1][1]) <= rows[r] <= max(e[0][1], e[1][1])]
        for c in range(C):
            out = 0 if red_or_green_ray((cols[c], rows[r]), near) else 1
            S[r + 1][c + 1] = out + S[r][c + 1] + S[r + 1][c] - S[r][c]
    best = 0
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, b = pts[i], pts[j]
            r0, r1 = sorted((ri[a[1]], ri[b[1]]))
            c0, c1 = sorted((ci[a[0]], ci[b[0]]))
            if S[r1 + 1][c1 + 1] - S[r0][c1 + 1] - S[r1 + 1][c0] + S[r0][c0] == 0:
                best = max(best, area(a, b))
    return best


def answer(pts, ok):
    es = edges(pts)
    best = 0
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, b = pts[i], pts[j]
            if area(a, b) > best and ok(a, b, es):
                best = area(a, b)
    return best


def flood_answer(pts):
    es = edges(pts)
    W = max(p[0] for p in pts) + 2
    H = max(p[1] for p in pts) + 2
    loop = {(x, y) for x in range(W + 1) for y in range(H + 1) if on_loop((x, y), es)}
    seen = {(-1, -1)}
    todo = [(-1, -1)]
    while todo:
        x, y = todo.pop()
        for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if -1 <= n[0] <= W and -1 <= n[1] <= H and n not in seen and n not in loop:
                seen.add(n)
                todo.append(n)
    good = lambda t: t not in seen
    best = 0
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, b = pts[i], pts[j]
            if area(a, b) > best and all(good((x, y)) for x in range(min(a[0], b[0]), max(a[0], b[0]) + 1)
                                         for y in range(min(a[1], b[1]), max(a[1], b[1]) + 1)):
                best = area(a, b)
    return best


def random_loop(rng, size):
    m = rng.randint(2, 5)
    xs = [rng.randint(0, size) for _ in range(m)]
    ys = [rng.randint(0, size) for _ in range(m)]
    pts = []
    for k in range(m):
        pts.append((xs[k], ys[k]))
        pts.append((xs[(k + 1) % m], ys[k]))
    # simple: every consecutive pair differs, and no tile is on two non-adjacent segments
    if any(p == q for p, q in edges(pts)):
        return None
    es = edges(pts)
    count = {}
    for i, (p, q) in enumerate(es):
        for x in range(min(p[0], q[0]), max(p[0], q[0]) + 1):
            for y in range(min(p[1], q[1]), max(p[1], q[1]) + 1):
                count.setdefault((x, y), set()).add(i)
    n = len(es)
    for t, segs in count.items():
        if len(segs) > 2 or (len(segs) == 2 and not any((a + 1) % n == b or (b + 1) % n == a for a in segs for b in segs if a != b)):
            return None
        if len(segs) == 2 and t not in pts:
            return None
    if len(set(pts)) != len(pts):
        return None
    return pts


def main():
    pts = parse(sys.argv[1])
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 9)
    xs = sorted(set(p[0] for p in pts))
    ys = sorted(set(p[1] for p in pts))
    print(f"points {len(pts)}; x {xs[0]}..{xs[-1]} ({len(xs)} distinct); y {ys[0]}..{ys[-1]} ({len(ys)} distinct)")
    print("columns 1 apart:", sum(1 for a, b in zip(xs, xs[1:]) if b - a == 1),
          "rows 1 apart:", sum(1 for a, b in zip(ys, ys[1:]) if b - a == 1))
    es = edges(pts)
    lens = sorted(((abs(p[0] - q[0]) + abs(p[1] - q[1])), p, q) for p, q in es)
    print("longest edges:", lens[-3:], "median length", lens[len(lens) // 2][0])
    print("part 1:", answer(pts, lambda a, b, es: True))
    for name, f in [("EDGE", lambda: answer(pts, edge_ok)), ("EDGE+IN", lambda: answer(pts, edge_in_ok)),
                    ("COMPRESS", lambda: compress_answer(pts))]:
        t = time.monotonic()
        v = f()
        print(f"part 2 {name}: {v}  ({time.monotonic() - t:.2f} s, CPython)")
    bad = {"EDGE": [], "EDGE+IN": [], "COMPRESS": [], "SPEC": [], "COMPRESS vs SPEC": []}
    done = 0
    spec_ok = lambda a, b, es: all(red_or_green_ray((x, y), es) for x in range(min(a[0], b[0]), max(a[0], b[0]) + 1)
                                   for y in range(min(a[1], b[1]), max(a[1], b[1]) + 1))
    while done < trials:
        loop = random_loop(rng, 9)
        if loop is None:
            continue
        done += 1
        truth = flood_answer(loop)
        spec = answer(loop, spec_ok)
        comp = compress_answer(loop)
        for name, v in [("EDGE", answer(loop, edge_ok)), ("EDGE+IN", answer(loop, edge_in_ok)),
                        ("COMPRESS", comp), ("SPEC", spec)]:
            if v != truth:
                bad[name].append((len(loop), loop, v, truth))
        if comp != spec:
            bad["COMPRESS vs SPEC"].append((len(loop), loop, comp, spec))
    for name, b in bad.items():
        b.sort()
        print(f"{name}: wrong on {len(b)} of {trials} random loops" + (f"; smallest: {b[0][1]} gives {b[0][2]}, truth {b[0][3]}" if b else ""))


main()
