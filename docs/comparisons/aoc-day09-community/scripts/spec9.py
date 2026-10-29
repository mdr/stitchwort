"""Check one loop: the Stitchwort spec's ray rule against a flood fill, tile by tile.

Usage: python3 -I spec9.py "x,y x,y ..."

Prints the floor with '#' on the loop, 'o' for tiles the spec calls inside,
'.' for tiles it calls outside, and marks with '!' (spec inside, flood
outside) or '?' (spec outside, flood inside) any tile where they differ. Then
the part 2 answer by the spec without compression, by the flood fill, and
by the compressed method.
"""
import importlib.util
import os
import sys

spec = importlib.util.spec_from_file_location("m", os.path.join(os.path.dirname(os.path.abspath(__file__)), "methods9.py"))
src = open(spec.origin).read().replace("\nmain()\n", "\n")
m = {}
exec(compile(src, spec.origin, "exec"), m)

pts = [tuple(map(int, p.split(","))) for p in sys.argv[1].split()]
es = m["edges"](pts)
W = max(p[0] for p in pts) + 2
H = max(p[1] for p in pts) + 2
loop = {(x, y) for x in range(-1, W + 1) for y in range(-1, H + 1) if m["on_loop"]((x, y), es)}
seen = {(-1, -1)}
todo = [(-1, -1)]
while todo:
    x, y = todo.pop()
    for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
        if -1 <= n[0] <= W and -1 <= n[1] <= H and n not in seen and n not in loop:
            seen.add(n)
            todo.append(n)
for y in range(H):
    row = ""
    for x in range(W):
        s = m["red_or_green_ray"]((x, y), es)
        f = (x, y) not in seen
        row += ("#" if (x, y) in loop else "o" if s and f else "." if not s and not f else "!" if s else "?")
    print(row)
specans = m["answer"](pts, lambda a, b, es: all(m["red_or_green_ray"]((x, y), es)
                     for x in range(min(a[0], b[0]), max(a[0], b[0]) + 1) for y in range(min(a[1], b[1]), max(a[1], b[1]) + 1)))
print("spec (no compression):", specans, " flood:", m["flood_answer"](pts), " compressed:", m["compress_answer"](pts))
