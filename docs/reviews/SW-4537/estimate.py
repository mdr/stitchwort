"""Whole-slice estimate from the ported sample. usage: python3 estimate.py results.csv [lines|chars]

Each stratum's draw was with probability proportional to a theorem's Stitchwort lines, so the mean of the
drawn theorems' ratios (port / Stitchwort) estimates the stratum's ratio; the slice's ratio is the strata's,
weighted by their Stitchwort lines (W below, from sample.py's table). The interval is a bootstrap: 10,000
resamples of the ratios with replacement inside each stratum, 5th and 95th percentiles.
"""
import sys, csv, random, collections
W = {'walk': 7032, 'two-run': 6850, 'readback': 10299, 'tree': 7035, 'lexer': 3575, 'settle': 7783,
     'printer': 27509, 'top': 1703}
unit = sys.argv[2] if len(sys.argv) > 2 else 'lines'
sfx = '_ch' if unit == 'chars' else ''
rows = list(csv.DictReader(open(sys.argv[1])))
def ratios(system):
    r = collections.defaultdict(list)
    for x in rows:
        sw = int(x['sw_stmt' + sfx]) + int(x['sw_proof' + sfx])
        r[x['stratum']].append((int(x[system + '_stmt' + sfx]) + int(x[system + '_proof' + sfx])) / sw)
    return r
def whole(r):
    w = sum(W[s] for s in r)
    return sum(W[s] * sum(v) / len(v) for s, v in r.items()) / w
rng = random.Random(4537)
for system in ('lean', 'rocq'):
    r = ratios(system)
    boot = sorted(whole({s: rng.choices(v, k=len(v)) for s, v in r.items()}) for _ in range(10000))
    cover = sum(W[s] for s in r) / sum(W.values())
    print(f"{system} / Stitchwort, {unit}: {whole(r):.2f} (90% interval {boot[500]:.2f} to {boot[9500]:.2f}); "
          f"{len(rows)} theorems, strata covering {100*cover:.0f}% of lines")
    for s, v in r.items(): print(f"  {s}: n={len(v)}, mean ratio {sum(v)/len(v):.2f}")
