import sys


def make(depth):
    if depth == 0:
        return (None, None)
    return (make(depth - 1), make(depth - 1))


def check(tree):
    left, right = tree
    return 1 if left is None else 1 + check(left) + check(right)


max_depth = int(sys.argv[1]) if len(sys.argv) > 1 else 18
min_depth = 4
stretch = max_depth + 1
print(f"stretch tree of depth {stretch}\t check: {check(make(stretch))}")
long_lived = make(max_depth)
for depth in range(min_depth, max_depth + 1, 2):
    count = 2 ** (max_depth - depth + min_depth)
    total = sum(check(make(depth)) for _ in range(count))
    print(f"{count}\t trees of depth {depth}\t check: {total}")
print(f"long lived tree of depth {max_depth}\t check: {check(long_lived)}")
