"""Check the part 2 shortcuts seen in the community against brute force, exhaustively.

Usage: python3 -I methods2.py MAX_LEN MAX_VALUE [INPUT]

Every report of 1..MAX_LEN levels drawn from 1..MAX_VALUE is checked by each
method below against the brute force (the puzzle's rule, and our spec). Prints,
per method, how many reports it gets wrong and the shortest one. With INPUT,
also prints each method's part 2 answer on that file.
"""
import itertools
import sys


def gentle_up(a, b):
    return 1 <= b - a <= 3


def chain(xs, ok):
    return all(ok(a, b) for a, b in zip(xs, xs[1:]))


def safe(xs):
    return chain(xs, gentle_up) or chain(xs, lambda a, b: gentle_up(b, a))


def brute(xs):
    return safe(xs) or any(safe(xs[:i] + xs[i + 1:]) for i in range(len(xs)))


def first_bad(xs, ok):
    return next((i for i, (a, b) in enumerate(zip(xs, xs[1:])) if not ok(a, b)), None)


def per_direction(xs):
    """Ours (Linear.sw): per direction, drop either level of the first bad step."""
    for ok in (gentle_up, lambda a, b: gentle_up(b, a)):
        i = first_bad(xs, ok)
        if i is None or chain(xs[:i] + xs[i + 1:], ok) or chain(xs[:i + 1] + xs[i + 2:], ok):
            return True
    return False


def bad_pair_mixed(xs):
    """First bad step of the whole check (direction from the first step); retry
    without either of its two levels. Misses reports fixed by dropping level 0."""
    if len(xs) < 2:
        return True
    up = xs[1] > xs[0]
    ok = gentle_up if up else (lambda a, b: gentle_up(b, a))
    i = first_bad(xs, ok)
    return i is None or safe(xs[:i] + xs[i + 1:]) or safe(xs[:i + 1] + xs[i + 2:])


def bad_triple_mixed(xs):
    """As above, also retrying without the level before the bad step."""
    if len(xs) < 2:
        return True
    up = xs[1] > xs[0]
    ok = gentle_up if up else (lambda a, b: gentle_up(b, a))
    i = first_bad(xs, ok)
    return i is None or any(safe(xs[:j] + xs[j + 1:]) for j in (i - 1, i, i + 1) if j >= 0)


def skip_greedy(xs):
    """One pass per direction: on a bad step, skip the later level once (keep the
    earlier one); a second bad step fails. Misses reports fixed by dropping the
    earlier level of the bad step."""
    for ok in (gentle_up, lambda a, b: gentle_up(b, a)):
        skipped, prev, good = False, xs[0], True
        for x in xs[1:]:
            if ok(prev, x):
                prev = x
            elif not skipped:
                skipped = True
            else:
                good = False
                break
        if good:
            return True
    return False


def count_bad(xs):
    """At most one bad step in some direction."""
    return any(sum(not ok(a, b) for a, b in zip(xs, xs[1:])) <= 1
               for ok in (gentle_up, lambda a, b: gentle_up(b, a)))


def bcs_diffs(xs):
    """bcs-aoc's Haskell (megathread m05enyh): over the differences, per direction."""
    for sign in (1, -1):
        ds = [(b - a) * sign for a, b in zip(xs, xs[1:])]

        def ok(d):
            return 1 <= d <= 3

        def go(ds):
            if len(ds) <= 1:
                return True
            x, y = ds[0], ds[1]
            if not ok(x) and not ok(y):
                return ok(x + y) and all(map(ok, ds[2:]))
            if len(ds) == 2:
                return True
            z = ds[2]
            if ok(x) and not ok(y) and ok(z):
                return (ok(x + y) or ok(y + z)) and all(map(ok, ds[3:]))
            if not ok(x):
                return all(map(ok, ds[1:]))
            return go(ds[1:])
        if go(ds):
            return True
    return False


def crvdgc_skip(xs):
    """crvdgc's Lean `isSafeRelaxed` (a while loop over the differences)."""
    def dec(ds):
        bad = lambda d: d < 1 or d > 3  # noqa: E731
        n, i, skipped = len(ds), 0, False
        while i < n:
            cur = ds[i]
            if bad(cur):
                if skipped:
                    return False
                if i == 0:
                    if i == n - 1:
                        return True
                    if bad(cur + ds[i + 1]):
                        skipped = True
                    else:
                        skipped = True
                        i += 1
                else:
                    if i == n - 1:
                        return True
                    if bad(cur + ds[i + 1]):
                        if bad(cur + ds[i - 1]):
                            return False
                        skipped = True
                    else:
                        skipped = True
                        i += 1
            i += 1
        return True
    ds = [b - a for a, b in zip(xs, xs[1:])]
    return dec(ds) or dec([-d for d in ds])


METHODS = [per_direction, bad_pair_mixed, bad_triple_mixed, skip_greedy, count_bad, bcs_diffs, crvdgc_skip]

n, v = int(sys.argv[1]), int(sys.argv[2])
wrong = {m.__name__: [0, None] for m in METHODS}
total = 0
for length in range(1, n + 1):
    for xs in itertools.product(range(1, v + 1), repeat=length):
        xs = list(xs)
        total += 1
        b = brute(xs)
        for m in METHODS:
            if m(xs) != b:
                w = wrong[m.__name__]
                w[0] += 1
                if w[1] is None:
                    w[1] = (xs, b)
print(f"{total} reports of 1..{n} levels from 1..{v}")
for name, (k, ex) in wrong.items():
    print(f"{name:18} wrong on {k:7}  first: {ex[0] if ex else '-'} (brute says {ex[1] if ex else '-'})")
if len(sys.argv) > 3:
    reports = [list(map(int, l.split())) for l in open(sys.argv[3]) if l.strip()]
    print("brute", sum(map(brute, reports)), " ".join(f"{m.__name__}={sum(map(m, reports))}" for m in METHODS))
