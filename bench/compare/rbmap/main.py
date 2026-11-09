import sys

# A persistent red-black tree as nested tuples: None is the leaf, a node is
# (red, left, key, value, right) with red a bool. Rebuilding the path on each
# insert is the benchmark; Python's dict would not do that work.

sys.setrecursionlimit(10000)


def balance_left(ins, key, value, right):
    # `ins` is the new left subtree of a black node (key, value, right).
    if ins is None:
        return None
    _, l, ky, vy, r2 = ins
    if l is not None and l[0]:
        _, ll, kx, vx, r1 = l
        return (True, (False, ll, kx, vx, r1), ky, vy, (False, r2, key, value, right))
    if r2 is not None and r2[0]:
        _, l2, kx, vx, r = r2
        return (True, (False, l, ky, vy, l2), kx, vx, (False, r, key, value, right))
    return (False, (True, l, ky, vy, r2), key, value, right)


def balance_right(left, key, value, ins):
    # `ins` is the new right subtree of a black node (left, key, value).
    if ins is None:
        return None
    _, l, ky, vy, r2 = ins
    if l is not None and l[0]:
        _, ll, kx1, vx1, r1 = l
        return (True, (False, left, key, value, ll), kx1, vx1, (False, r1, ky, vy, r2))
    if r2 is not None and r2[0]:
        _, l2, kx2, vx2, r3 = r2
        return (True, (False, left, key, value, l), ky, vy, (False, l2, kx2, vx2, r3))
    return (False, left, key, value, (True, l, ky, vy, r2))


def is_red(tree):
    return tree is not None and tree[0]


def ins(tree, key, value):
    if tree is None:
        return (True, None, key, value, None)
    red, a, ky, vy, b = tree
    if red:
        if key < ky:
            return (True, ins(a, key, value), ky, vy, b)
        if key == ky:
            return (True, a, key, value, b)
        return (True, a, ky, vy, ins(b, key, value))
    if key < ky:
        if is_red(a):
            return balance_left(ins(a, key, value), ky, vy, b)
        return (False, ins(a, key, value), ky, vy, b)
    if key == ky:
        return (False, a, key, value, b)
    if is_red(b):
        return balance_right(a, ky, vy, ins(b, key, value))
    return (False, a, ky, vy, ins(b, key, value))


def set_black(tree):
    if tree is None:
        return None
    _, l, k, v, r = tree
    return (False, l, k, v, r)


def insert(tree, key, value):
    if is_red(tree):
        return set_black(ins(tree, key, value))
    return ins(tree, key, value)


def fold(tree, acc, step):
    # In key order; the tree is shallow, the recursion is not deep.
    if tree is None:
        return acc
    _, l, k, v, r = tree
    return fold(r, step(k, v, fold(l, acc, step)), step)


count = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
tree = None
for key in range(count - 1, -1, -1):
    tree = insert(tree, key, key % 10 == 0)
print(fold(tree, 0, lambda k, v, acc: acc + 1 if v else acc))
