"""Rough counts of top-level `def`s, their arms (`  |` lines), and those with
`if`, `match` or `decreasing`, over the `.sw` files under a folder, by regular
expressions: close, not exact. Usage: python3 count.py crates/elab/src/std"""
import re, sys, pathlib, collections

root = pathlib.Path(sys.argv[1])
stats = collections.Counter()
armhist = collections.Counter()
for p in root.rglob('*.sw'):
    lines = p.read_text().split('\n')
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^(export\s+)?(opaque\s+)?(def|theorem|instance)\s', l)
        if m:
            kind = m.group(3)
            stats[kind] += 1
            if m.group(2):
                stats['opaque'] += 1
            j = i + 1
            arms = 0
            dec = 'decreasing' in l and '[decreasing' not in l
            matches = 0
            ifs = 0
            while j < len(lines) and (lines[j].startswith(' ') or lines[j] == '' or lines[j].startswith(':=')):
                t = lines[j]
                if re.match(r'^\s{2}\|', t):
                    arms += 1
                if re.match(r'^\s*decreasing\b', t):
                    dec = True
                if re.search(r'\bmatch\b', t):
                    matches += 1
                if re.search(r'\bif\b', t):
                    ifs += 1
                j += 1
            if kind == 'def':
                stats['def_arms_total'] += arms
                if arms > 0:
                    stats['def_with_arms'] += 1
                armhist[min(arms, 10)] += 1
                if dec:
                    stats['decreasing'] += 1
                if matches:
                    stats['def_with_match'] += 1
                if ifs:
                    stats['def_with_if'] += 1
            i = j
            continue
        i += 1
print(dict(stats))
print(sorted(armhist.items()))
