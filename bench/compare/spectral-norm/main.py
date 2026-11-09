import math
import sys


def entry(i, j):
    return 1.0 / ((i + j) * (i + j + 1) // 2 + i + 1)


def apply(size, transposed, vector):
    if transposed:
        return [sum(entry(j, i) * vector[j] for j in range(size)) for i in range(size)]
    return [sum(entry(i, j) * vector[j] for j in range(size)) for i in range(size)]


def normal(size, vector):
    return apply(size, True, apply(size, False, vector))


size = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
u = [1.0] * size
for _ in range(10):
    v = normal(size, u)
    u = normal(size, v)
v_bv = sum(x * y for x, y in zip(u, v))
vv = sum(y * y for y in v)
print("%0.9f" % math.sqrt(v_bv / vv))
