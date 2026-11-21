"""Whole-slice and per-stratum estimates from the ported sample.

usage: python3 estimate.py results.csv [--drop NAME] [--impute NAME] [--seed N]

Each stratum's draw was with probability proportional to a theorem's Stitchwort lines x (statement plus
proof), so for any count q, X_s * mean(q_i / x_i) estimates the stratum's total of q (Hansen-Hurwitz),
where X_s is the stratum's Stitchwort lines (W below, from sample.py's table). A stratum's ratio for a
measure (lines or non-blank characters; statement, proof or both) is the estimated port total over the
estimated Stitchwort total: mean(port_i / x_i) / mean(sw_i / x_i). For lines of the whole theorem this
is the plain mean of the drawn theorems' ratios. The slice's ratio adds the strata's estimated totals:
for lines, Stitchwort's totals are known (STMT, PROOF, W below) and used as weights; for characters,
Stitchwort's totals are estimated the same way as the ports'.

The interval is a bootstrap: 10,000 resamples of the theorems with replacement inside each stratum,
5th and 95th percentiles. With 2 or 3 draws a stratum's own interval is too narrow; `range` gives the
smallest and largest per-theorem ratio seen.

--drop NAME leaves a theorem out (its reserve, if ported, is a row of its own). --impute NAME keeps the
theorem's Stitchwort counts and sets each port count to the largest whole-theorem ratio (port / Stitchwort,
for that system, in lines or characters) among the other theorems of its stratum, times its Stitchwort
count, statement and proof alike: the note's second treatment of a set-aside.
"""
import sys, csv, random, collections
W = {'walk': 7032, 'two-run': 6850, 'readback': 10299, 'tree': 7035, 'lexer': 3575, 'settle': 7783,
     'printer': 27509, 'top': 1703}
STMT = {'walk': 2885, 'two-run': 3009, 'readback': 2463, 'tree': 2393, 'lexer': 1059, 'settle': 1853,
        'printer': 7619, 'top': 445}
PROOF = {s: W[s] - STMT[s] for s in W}
ORDER = list(W)
args = sys.argv[1:]
opt = lambda flag: args[args.index(flag) + 1] if flag in args else None
drop, impute, seed = opt('--drop'), opt('--impute'), int(opt('--seed') or 4537)
rows = [x for x in csv.DictReader(open(args[0])) if x['name'] != drop]
for x in rows:
    for k in list(x):
        if k not in ('stratum', 'name', 'role'): x[k] = int(x[k])
    x['x'] = x['sw_stmt'] + x['sw_proof']
COLS = {'stmt': ['_stmt'], 'proof': ['_proof'], 'both': ['_stmt', '_proof']}
def q(x, system, part, unit):
    sfx = '_ch' if unit == 'chars' else ''
    return sum(x[system + c + sfx] for c in COLS[part])
if impute:
    t = next(x for x in rows if x['name'] == impute)
    others = [x for x in rows if x['stratum'] == t['stratum'] and x is not t]
    for system in ('lean', 'rocq'):
        for sfx in ('', '_ch'):
            both = lambda x, who: x[who + '_stmt' + sfx] + x[who + '_proof' + sfx]
            worst = max(both(x, system) / both(x, 'sw') for x in others)
            for c in ('_stmt', '_proof'): t[system + c + sfx] = round(worst * t['sw' + c + sfx])
by = collections.defaultdict(list)
for x in rows: by[x['stratum']].append(x)
def totals(sample, system, part, unit):
    """Estimated (port, Stitchwort) totals per stratum."""
    out = {}
    for s, xs in sample.items():
        port = W[s] * sum(q(x, system, part, unit) / x['x'] for x in xs) / len(xs)
        if unit == 'lines': sw = {'stmt': STMT, 'proof': PROOF, 'both': W}[part][s]
        else: sw = W[s] * sum(q(x, 'sw', part, unit) / x['x'] for x in xs) / len(xs)
        out[s] = (port, sw)
    return out
def ratios(sample, system, part, unit):
    t = totals(sample, system, part, unit)
    if unit == 'lines':   # Stitchwort's line totals are known: scale the stratum's ratio estimate by them
        r = {s: (sum(q(x, system, part, unit) / x['x'] for x in sample[s]) /
                 sum(q(x, 'sw', part, unit) / x['x'] for x in sample[s])) for s in sample}
        known = {'stmt': STMT, 'proof': PROOF, 'both': W}[part]
        whole = sum(r[s] * known[s] for s in r) / sum(known[s] for s in r)
    else:
        r = {s: p / w for s, (p, w) in t.items()}
        whole = sum(p for p, _ in t.values()) / sum(w for _, w in t.values())
    return r, whole
rng = random.Random(seed)
boots = [{s: rng.choices(xs, k=len(xs)) for s, xs in by.items()} for _ in range(10000)]
def interval(vals):
    v = sorted(vals); return v[500], v[9500]
print(f"{len(rows)} theorems" + (f", {drop} dropped" if drop else '') + (f", {impute} imputed" if impute else ''))
for unit in ('lines', 'chars'):
    for part in ('both', 'stmt', 'proof'):
        print(f"\n## {unit}, {part}")
        print('| Stratum | n | Lean / SW | 90% | range | Rocq / SW | 90% | range |')
        print('|---|---|---|---|---|---|---|---|')
        res = {}
        for system in ('lean', 'rocq'):
            r, whole = ratios(by, system, part, unit)
            bs = [ratios(b, system, part, unit) for b in boots]
            res[system] = (r, whole, bs)
        for s in ORDER + ['slice']:
            cells = []
            for system in ('lean', 'rocq'):
                r, whole, bs = res[system]
                if s == 'slice':
                    lo, hi = interval(b[1] for b in bs); cells += [f"**{whole:.2f}**", f"{lo:.2f} to {hi:.2f}", '']
                else:
                    lo, hi = interval(b[0][s] for b in bs)
                    each = [q(x, system, part, unit) / q(x, 'sw', part, unit) for x in by[s] if q(x, 'sw', part, unit)]
                    cells += [f"{r[s]:.2f}", f"{lo:.2f} to {hi:.2f}", f"{min(each):.2f} to {max(each):.2f}"]
            n = len(rows) if s == 'slice' else len(by[s])
            print(f"| {s} | {n} | " + ' | '.join(cells) + ' |')
