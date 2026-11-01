#!/usr/bin/env python3
"""First-sentence lengths of the `--` blocks above std definitions (not
theorems), and the summaries of the names given. Usage: summ.py ROOT [NAME...]"""
import os, re, sys
DECL = re.compile(r'^(def|theorem|type|instance|ability|opaque|interface)\b\s*([A-Za-z0-9_.%\']*)')
def first_sentence(text):
    tick = False
    for i, c in enumerate(text):
        if c == '`': tick = not tick
        if c == '.' and not tick and (i + 1 == len(text) or text[i+1] == ' '):
            if text[max(0,i-3):i+1] in ('e.g.', 'i.e.') : continue
            return text[:i+1]
    return text
lens = []; samples = []
for dp, _, fs in os.walk(sys.argv[1]):
    for f in fs:
        if not f.endswith('.sw'): continue
        lines = open(os.path.join(dp, f), encoding='utf-8').read().split('\n')
        for i, l in enumerate(lines):
            m = DECL.match(l)
            if not m or m.group(1) == 'theorem': continue
            j = i - 1
            while j >= 0 and lines[j].startswith('@['): j -= 1
            b = []
            while j >= 0 and lines[j].startswith('--'):
                b.append(lines[j][2:].strip()); j -= 1
            if not b: continue
            b.reverse()
            para = []
            for x in b:
                if not x: break
                para.append(x)
            s = first_sentence(' '.join(para))
            lens.append(len(s))
            if m.group(2) in sys.argv[2:]: samples.append((m.group(2), s))
lens.sort()
n = len(lens)
print('n', n, 'median', lens[n//2], 'p90', lens[int(n*.9)], 'max', lens[-1], '>160:', sum(1 for x in lens if x > 160))
for s in samples: print(s)
