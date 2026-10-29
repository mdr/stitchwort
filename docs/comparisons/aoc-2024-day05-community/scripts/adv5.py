"""Test the day 5 shortcuts on adversarial rule sets, exhaustively on small cases.

Usage: python3 -I adv5.py [INPUT]

Every relation on pages {1..4} (each of the 12 ordered pairs is a rule or not:
4,096 rule sets) against every update that is an ordering of 3 or 4 of those
pages (48 updates): 196,608 cases. Each case is classed by the rules restricted
to the update's pages:

  A  strict total order (asymmetric, total, transitive): our proofs' assumption
  B  acyclic with exactly one valid order, but some pair has no rule of its own
     (the order only follows by transitivity, as in 1|2, 2|3 with no 1|3)
  C  acyclic with more than one valid order (the puzzle's "the" order is
     ambiguous; some cases still agree on the middle page)
  D  a cycle (no valid order exists)

Part 1 methods are judged against the puzzle's rule ("no page comes after a
page it must precede", all pairs). Part 2 methods are judged by whether they
return a valid order (one that breaks no rule), and in B whether it is the
unique one. With INPUT (the real day05.txt) it also reports the input's
structure and checks every method agrees on it.
"""
import functools
import itertools
import sys
from collections import Counter

sys.setrecursionlimit(200)


# ---- part 1 checks -------------------------------------------------------
def p1_all_pairs(rule, u):  # ours, and most careful solutions
    return all(not rule(u[j], u[i]) for i in range(len(u)) for j in range(i + 1, len(u)))


def p1_adjacent(rule, u):  # is_sorted with the comparator: only neighbours
    return all(not rule(b, a) for a, b in zip(u, u[1:]))


def p1_adjacent_forward(rule, u):  # "each neighbour pair has a rule a|b"
    return all(rule(a, b) for a, b in zip(u, u[1:]))


def p1_sort_compare(rule, u):  # sorted(u, cmp) == u
    return p2_cmp(rule, u) == list(u)


# ---- part 2 orderings ----------------------------------------------------
def p2_stitchwort(rule, u):
    """List.sortWith (bottom-up merge sort, std List/Sort.sw) with our test."""
    le = lambda page, nxt: not rule(nxt, page)

    def merge(xs, ys):
        out, i, j = [], 0, 0
        while i < len(xs) and j < len(ys):
            if le(xs[i], ys[j]):
                out.append(xs[i]); i += 1
            else:
                out.append(ys[j]); j += 1
        return out + xs[i:] + ys[j:]

    runs = []  # slot k: None or a run, like List.buildRuns/pushRun
    for x in u:
        run, k = [x], 0
        while True:
            if k == len(runs):
                runs.append(run); break
            if runs[k] is None:
                runs[k] = run; break
            run = merge(runs[k], run); runs[k] = None; k += 1
    acc = []
    for r in runs:  # List.mergeRuns: older on the left
        if r is not None:
            acc = merge(r, acc)
    return acc


def p2_cmp(rule, u):  # sorted(key=cmp_to_key(...)) with a three-way comparator
    c = lambda a, b: -1 if rule(a, b) else (1 if rule(b, a) else 0)
    return sorted(u, key=functools.cmp_to_key(c))


def p2_cmp2(rule, u):  # two-valued comparator: -1 if a|b else 1
    c = lambda a, b: -1 if rule(a, b) else 1
    return sorted(u, key=functools.cmp_to_key(c))


def p2_count(rule, u):  # sort by how many of the update's pages must precede
    return sorted(u, key=lambda p: sum(rule(q, p) for q in u))


def p2_kahn(rule, u):  # topological sort of the rules restricted to the update
    left, out = list(u), []
    while left:
        ready = [p for p in left if not any(rule(q, p) for q in left if q != p)]
        if not ready:
            raise ValueError("cycle")
        out.append(ready[0]); left.remove(ready[0])
    return out


def p2_dfs(rule, u):  # Thierry Martinez's day05.py: DFS, predecessors first
    out = []

    def add(p):
        if p in out:
            return
        for q in u:
            if rule(q, p):
                add(q)
        out.append(p)
    for p in u:
        add(p)
    return out


def p2_swap(rule, u, cap=1000):  # swap the first broken pair until none
    u = list(u)
    for _ in range(cap):
        bad = next(((i, j) for i in range(len(u)) for j in range(i + 1, len(u)) if rule(u[j], u[i])), None)
        if bad is None:
            return u
        i, j = bad
        u[i], u[j] = u[j], u[i]
    raise TimeoutError("no fixpoint")


P1 = {"all pairs (ours)": p1_all_pairs, "neighbours only (is_sorted)": p1_adjacent,
      "neighbours have a rule a|b": p1_adjacent_forward, "sort, then compare": p1_sort_compare}
P2 = {"Stitchwort sortWith (ours)": p2_stitchwort, "cmp_to_key, 3-way": p2_cmp, "cmp_to_key, 2-way": p2_cmp2,
      "sort by predecessor count": p2_count, "Kahn on the update": p2_kahn, "DFS on the update": p2_dfs,
      "swap until fixed": p2_swap}


def valid_orders(rule, pages):
    return [p for p in itertools.permutations(pages) if p1_all_pairs(rule, p)]


def classify(rule, pages):
    vs = valid_orders(rule, pages)
    if not vs:
        return "D", vs
    if len(vs) > 1:
        return "C", vs
    total = all(rule(a, b) or rule(b, a) for a, b in itertools.combinations(pages, 2))
    return ("A" if total else "B"), vs


def run(fn, rule, u):
    try:
        return fn(rule, u)
    except RecursionError:
        return "recursion"
    except TimeoutError:
        return "loops"
    except ValueError:
        return "error"


def small():
    pairs = [(a, b) for a in range(1, 5) for b in range(1, 5) if a != b]
    updates = [p for k in (3, 4) for s in itertools.combinations(range(1, 5), k) for p in itertools.permutations(s)]
    p1_wrong = {k: Counter() for k in P1}
    p2_res = {k: Counter() for k in P2}
    classes = Counter()
    first = {}
    ambiguous_mid = 0
    for mask in range(1 << len(pairs)):
        rs = {pairs[i] for i in range(len(pairs)) if mask >> i & 1}
        rule = lambda a, b, rs=rs: (a, b) in rs
        for u in updates:
            cls, vs = classify(rule, u)
            classes[cls] += 1
            if cls == "C" and len({v[len(v) // 2] for v in vs}) > 1:
                ambiguous_mid += 1
            truth = p1_all_pairs(rule, u)
            for k, f in P1.items():
                if f(rule, u) != truth:
                    p1_wrong[k][cls] += 1
                    first.setdefault(("p1", k, cls), (sorted(rs), u))
            for k, f in P2.items():
                r = run(f, rule, u)
                if isinstance(r, str):
                    p2_res[k][(cls, r)] += 1
                elif tuple(r) in vs:
                    p2_res[k][(cls, "valid")] += 1
                else:
                    p2_res[k][(cls, "invalid order")] += 1
                    first.setdefault(("p2", k, cls), (sorted(rs), u, r))
    print("cases by class:", dict(sorted(classes.items())), "| C cases whose valid orders disagree on the middle:", ambiguous_mid)
    print("\npart 1: wrong verdicts by class")
    for k, c in p1_wrong.items():
        print(f"  {k:30} {dict(sorted(c.items())) or 'none'}")
    print("\npart 2: outcome by class (counts)")
    for k, c in p2_res.items():
        print(f"  {k:28}", ", ".join(f"{a}:{b}={n}" for (a, b), n in sorted(c.items())))
    print("\nfirst failures:")
    for key, v in first.items():
        print(" ", key, v)


def real(path):
    text = open(path).read().strip().split("\n\n")
    rules = {tuple(map(int, l.split("|"))) for l in text[0].split("\n")}
    ups = [list(map(int, l.split(","))) for l in text[1].split("\n")]
    rule = lambda a, b: (a, b) in rules
    pages = sorted({p for r in rules for p in r})
    pairs = sum(1 for a, b in itertools.combinations(pages, 2) if rule(a, b) or rule(b, a))
    both = sum(1 for a, b in itertools.combinations(pages, 2) if rule(a, b) and rule(b, a))
    print(f"rules {len(rules)}, pages in rules {len(pages)}, unordered pairs {len(pages) * (len(pages) - 1) // 2}, "
          f"pairs with a rule {pairs}, pairs ordered both ways {both}")
    outdeg = Counter(a for a, _ in rules)
    print("rules per page (as X):", sorted(Counter(outdeg.values()).items()))
    # a short cycle in the whole rule set
    cyc = next(((a, b, c) for (a, b) in rules for c in pages if rule(b, c) and rule(c, a)), None)
    print("a 3-cycle in the whole rule set:", cyc)
    lens = Counter(len(u) for u in ups)
    print("updates", len(ups), "lengths", min(lens), "to", max(lens))
    print("update classes:", Counter(classify_fast(rule, u) for u in ups))
    for k, f in P1.items():
        print(f"  part 1 {k:30}", sum(u[len(u) // 2] for u in ups if f(rule, u)))
    bad = [u for u in ups if not p1_all_pairs(rule, u)]
    for k, f in P2.items():
        print(f"  part 2 {k:30}", sum(run(f, rule, u)[len(u) // 2] for u in bad))


def classify_fast(rule, u):
    total = all(rule(a, b) != rule(b, a) for a, b in itertools.combinations(u, 2))
    trans = all(not (rule(a, b) and rule(b, c)) or rule(a, c) for a in u for b in u for c in u)
    return "A" if total and trans and len(set(u)) == len(u) else "not A"


if __name__ == "__main__":
    if len(sys.argv) > 1:
        real(sys.argv[1])
        print()
    small()
