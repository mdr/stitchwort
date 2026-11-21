"""The seeded sample of docs/reviews/SW-4483-byfacts-in-context.md, §3.

Draws theorems at random from five pools, counting a theorem as its
statement and proof up to the next blank line, as SW-4464 and closer.md do.
Run from anywhere: python3 docs/reviews/SW-4483/sample.py [max lines shown]
"""
import fnmatch, os, random, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
SEED = 4483

def theorems(path):
    out = []; lines = open(path).read().split('\n'); i = 0
    while i < len(lines):
        m = re.match(r'\s*theorem\s+([A-Za-z0-9_.]+)', lines[i])
        if m:
            j = i
            while j < len(lines) and lines[j].strip() != '': j += 1
            out.append((m.group(1), i + 1, lines[i:j])); i = j
        else: i += 1
    return out

def files(d):
    for r, _, fs in os.walk(os.path.join(ROOT, d)):
        if '/Tests' in r: continue
        for f in sorted(fs):
            if f.endswith('.sw'): yield os.path.join(r, f)

# closer.md's pools (its §1), left out of "formatter, elsewhere".
CLOSER = ['Fmt/Kinds.sw', 'Fmt/SpellProofs.sw', 'Fmt/TokenProofs.sw', 'Syntax/Settle*Proofs.sw',
          'Fmt/Spacing*Proofs.sw', 'Syntax/ParseWalk*.sw', 'Syntax/ParseProofs.sw',
          'Fmt/JoinProofs.sw', 'Fmt/PassProofs.sw', 'Fmt/TreeJoinProofs.sw', 'Fmt/GlueProofs.sw']

def pool(dirs, skip=()):
    out = []
    for d in dirs:
        for p in sorted(files(d)):
            rel = os.path.relpath(p, ROOT)
            if any(fnmatch.fnmatch(rel, 'tools/fmt/src/' + g) for g in skip): continue
            for n, l, b in theorems(p): out.append((rel, l, n, b))
    return out

POOLS = [('std', ['crates/elab/src/std'], (), 10), ('aoc', ['aoc/src'], (), 10),
         ('rogue', ['games/rogue'], (), 6), ('apps', ['apps'], (), 6),
         ('fmt-other', ['tools/fmt/src'], CLOSER, 4), ('toyfmt', ['tools/toyfmt'], (), 4)]

if __name__ == '__main__':
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
    r = random.Random(SEED)
    for name, dirs, skip, k in POOLS:
        p = pool(dirs, skip)
        print(f'=========== POOL {name}: {len(p)} theorems, {sum(len(b) for *_, b in p)} lines')
        for path, l, n, b in r.sample(p, k):
            print(f'### [{name}] {path}:{l} {n} ({len(b)} lines)')
            print('\n'.join(b[:cap]))
            if len(b) > cap: print(f'  … {len(b) - cap} more lines')
            print()
