"""Means of scores.csv, overall and by proof length. usage: python3 means.py scores.csv ../SW-4537/results.csv"""
import csv, sys
rows = list(csv.DictReader(open(sys.argv[1])))
proof = {r['name']: int(r['sw_proof']) for r in csv.DictReader(open(sys.argv[2]))}
cols = [c for c in rows[0] if c not in ('stratum', 'name')]
def mean(rs, c): return sum(int(r[c]) for r in rs) / len(rs)
groups = {'all': rows, 'short (proof <= 15 lines)': [r for r in rows if proof[r['name']] <= 15],
          'long (proof > 15 lines)': [r for r in rows if proof[r['name']] > 15]}
for label, rs in groups.items():
    print(label, len(rs), ' '.join(f'{c}={mean(rs, c):.1f}' for c in cols))
for s in ('sw', 'lean', 'rocq'):
    print(s, 'total of S+N+T', f'{sum(mean(rows, f"{s}_{k}") for k in "snt"):.1f}')
for k in 'snt':
    print(k, 'SW ahead / level / behind Lean:', *[sum(1 for r in rows if f(int(r[f'sw_{k}']), int(r[f'lean_{k}'])))
          for f in (lambda a, b: a > b, lambda a, b: a == b, lambda a, b: a < b)],
          ' Rocq:', *[sum(1 for r in rows if f(int(r[f'sw_{k}']), int(r[f'rocq_{k}'])))
          for f in (lambda a, b: a > b, lambda a, b: a == b, lambda a, b: a < b)])
print('no doc:', sum(1 for r in rows if r['doc'] == '1'))
