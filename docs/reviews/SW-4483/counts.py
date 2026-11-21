"""Counts for docs/reviews/SW-4483-byfacts-in-context.md, §3.3: how often each
project spells conjunction handling by hand, and how often it uses a finisher.
Lines of .sw files outside Tests folders."""
import os, re
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
PATTERNS = [('Bool.and*', r'Bool\.(andLeft|andRight|andIntro)'), ('And./.left/.right', r'And\.(left|right)|\.(left|right)\b'),
            ('Both', r'\bBoth\b'), ('cases', r'(?<![.\w])cases\b'), ('arithmetic', r'\barithmetic\b'),
            ('rewrite repeatedly', r'rewrite repeatedly'), ('byWalking', r'\bbyWalking\b'), ('theorem', r'^\s*theorem\s'),
            ('Witness/Exists.elim', r'\bWitness\b|Exists\.elim'),
            ('arithmetic [..]', r'arithmetic \[[^\]]'),
            ('arithmetic [..] naming a part of a fact', r'arithmetic \[[^\]]*(\.left|\.right|And\.left|And\.right|andLeft|andRight)'),
            ('arithmetic [] in a tuple', r'\(arithmetic \[\]\)'),
            ('line is only a let of a part of a fact', r'^\s*let \w+(: [^=]*)? := (Bool\.and(Left|Right) \(?[\w.]+|And\.(left|right) \w+|\w+\.(left|right)(\.(left|right))*)\)*\s*$|^\s*let (Both|\() ?[\w ,()]+\)? := \w+\s*$')]
print('| Project | Lines | ' + ' | '.join(n for n, _ in PATTERNS) + ' |')
print('|---|---|' + '---|' * len(PATTERNS))
for d in ['crates/elab/src/std', 'aoc/src', 'games/rogue', 'apps', 'tools/fmt/src', 'tools/toyfmt']:
    lines = []
    for r, _, fs in os.walk(os.path.join(ROOT, d)):
        if '/Tests' in r: continue
        for f in fs:
            if f.endswith('.sw'): lines += open(os.path.join(r, f)).read().split('\n')
    print(f'| `{d}` | {len(lines)} | ' + ' | '.join(str(sum(1 for l in lines if re.search(p, l))) for _, p in PATTERNS) + ' |')
