import sys
import threading

# Expressions are tuples: ("var", name), ("val", value), ("add", left, right),
# ("mul", left, right). Reassociating makes chains as long as the tree has
# leaves, so the recursion needs a deep stack (Lean's original sets 4 GB).


def mk_expr(depth, value):
    if depth == 0:
        return ("var", 1) if value == 0 else ("val", value)
    return ("add", mk_expr(depth - 1, value + 1), mk_expr(depth - 1, max(value - 1, 0)))


def append_add(e1, e2):
    if e1[0] == "add":
        return ("add", e1[1], append_add(e1[2], e2))
    return ("add", e1, e2)


def append_mul(e1, e2):
    if e1[0] == "mul":
        return ("mul", e1[1], append_mul(e1[2], e2))
    return ("mul", e1, e2)


def reassoc(e):
    if e[0] == "add":
        return append_add(reassoc(e[1]), reassoc(e[2]))
    if e[0] == "mul":
        return append_mul(reassoc(e[1]), reassoc(e[2]))
    return e


def const_folding(e):
    tag = e[0]
    if tag != "add" and tag != "mul":
        return e
    e1 = const_folding(e[1])
    e2 = const_folding(e[2])
    combine = (lambda a, b: a + b) if tag == "add" else (lambda a, b: a * b)
    if e1[0] == "val":
        if e2[0] == "val":
            return ("val", combine(e1[1], e2[1]))
        if e2[0] == tag:
            if e2[2][0] == "val":
                return (tag, ("val", combine(e1[1], e2[2][1])), e2[1])
            if e2[1][0] == "val":
                return (tag, ("val", combine(e1[1], e2[1][1])), e2[2])
    return (tag, e1, e2)


def evaluate(e):
    tag = e[0]
    if tag == "var":
        return 0
    if tag == "val":
        return e[1]
    if tag == "add":
        return evaluate(e[1]) + evaluate(e[2])
    return evaluate(e[1]) * evaluate(e[2])


def main():
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    for start in range(1, rounds + 1):
        e = mk_expr(depth, start)
        before = evaluate(e)
        after = evaluate(const_folding(reassoc(e)))
        print(f"{before} {after}")


sys.setrecursionlimit(1 << 30)
threading.stack_size(1 << 30)
thread = threading.Thread(target=main)
thread.start()
thread.join()
