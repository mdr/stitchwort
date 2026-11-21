"""Strata and the seeded sample for SW-4537.

usage: python3 sample.py <tools/fmt/src> <theorems.json from SW-4519/count.py> [--draw]

Strata are by what a theorem concludes (parser relations, as SW-4519 2.2)
and, for the rest, by file. The draw is with replacement inside each
stratum, with probability proportional to a theorem's statement + proof
lines, so the mean of the drawn theorems' ratios estimates the stratum's
line ratio directly.
"""
import sys, json, re, random, collections

SEED = 4537
N_MAIN = 30       # theorems to port
N_RESERVE = 3     # per stratum, used in order when a draw is set aside
root, tj = sys.argv[1], sys.argv[2]

FILES = [  # first match wins; for theorems with no parser relation in the conclusion
    ('top',     r'Fmt/(Accepts1|Driver1|TopStatements|TopReadBack|Grammar1|OutputStatements|Predicates|TriviaStatements|ReadBackFile|CommentsKeptProof|MeaningProofs)\.sw'),
    ('readback', r'Syntax/ReadBack'),
    ('lexer',   r'Syntax/Lex|Fmt/(FileLex|PrintLex|Token|SourcePlain)'),
    ('settle',  r'Syntax/(Settle|OnceUnreturned)|Fmt/(Settle|Unreturned|Split|Mark|Finish)'),
    ('tree',    r'Syntax/'),
    ('printer', r'Fmt/'),
]
def conclusion(lines, t):
    s = ' '.join(lines[t['line'] - 1: t['line'] - 1 + t['stmt']])
    i = s.rfind('):')
    return s[i:] if i >= 0 else s
def stratum(t, src):
    c = conclusion(src[t['file']], t)
    if re.search(r'\bFollows\b', c): return 'two-run'
    if re.search(r'\b(Gives|ReadsAt|ReadsIn|Reads0)\b', c): return 'walk'
    if re.search(r'\b(Runs|RunsFrom)\b|\b\w+Reads\b', c): return 'readback'
    for name, pat in FILES:
        if re.match(pat, t['file']): return name
    raise SystemExit('unfiled: ' + t['file'])

ts = [t for t in json.load(open(tj)) if 'Tests/' not in t['file']]
src = {}
for t in ts:
    if t['file'] not in src: src[t['file']] = open(root + '/' + t['file']).read().split('\n')
    t['stratum'] = stratum(t, src)
    t['size'] = t['stmt'] + t['proof']
by = collections.defaultdict(list)
for t in ts: by[t['stratum']].append(t)
order = ['walk', 'two-run', 'readback', 'tree', 'lexer', 'settle', 'printer', 'top']
total = sum(t['size'] for t in ts)
print('| Stratum | Theorems | Statement lines | Proof lines | Both | Share | Median size | Draws |')
print('|---|---|---|---|---|---|---|---|')
# allocation: proportional to lines, at least 2 a stratum, largest remainders
quota = {s: max(2, N_MAIN * sum(t['size'] for t in by[s]) / total) for s in order}
scale = N_MAIN / sum(quota.values())
alloc = {s: max(2, int(quota[s] * scale)) for s in order}
rem = sorted(order, key=lambda s: quota[s] * scale - int(quota[s] * scale), reverse=True)
i = 0
while sum(alloc.values()) < N_MAIN: alloc[rem[i % len(rem)]] += 1; i += 1
for s in order:
    g = by[s]; sz = sorted(t['size'] for t in g)
    print(f"| {s} | {len(g)} | {sum(t['stmt'] for t in g)} | {sum(t['proof'] for t in g)} | {sum(sz)} | {100*sum(sz)/total:.1f}% | {sz[len(sz)//2]} | {alloc[s]} |")
print(f"| all | {len(ts)} | {sum(t['stmt'] for t in ts)} | {sum(t['proof'] for t in ts)} | {total} | | | {sum(alloc.values())} |")
if '--draw' in sys.argv:
    rng = random.Random(SEED)
    out = []
    for s in order:
        g = sorted(by[s], key=lambda t: (t['file'], t['line']))
        picks = rng.choices(g, weights=[t['size'] for t in g], k=alloc[s] + N_RESERVE)
        for k, t in enumerate(picks):
            role = 'main' if k < alloc[s] else 'reserve'
            out.append(dict(stratum=s, role=role, n=k + 1, name=t['name'], file=t['file'], line=t['line'], stmt=t['stmt'], proof=t['proof']))
            print(f"| {s} | {k+1} {role} | `{t['name']}` | `{t['file']}:{t['line']}` | {t['stmt']} | {t['proof']} |")
    json.dump(out, open('sample.json', 'w'), indent=1)
