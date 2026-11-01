#!/usr/bin/env python3
"""Count declarations with a `--` comment block directly above (the
formatter.md convention), per tree and kind, and how many blocks hold
maintainer notes. Usage: doccov.py ROOT [ROOT...]  (run from the repo root)."""
import os, re, sys, collections

DECL = re.compile(r'^(def|theorem|type|instance|ability|opaque|interface)\b\s*([A-Za-z0-9_.%\']*)')
MAINT = {
    'ticket': re.compile(r'\bSW-\d+'),
    'dnum': re.compile(r'\bD\d{3,4}\b'),
    'proposal': re.compile(r'docs/|proposals?/|\.md\b'),
    # No 'timing' marker: review 1 found its hits were cost notes users need.
}

def blocks(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if kind == 'opaque':
            kind = 'def'
        j = i - 1
        while j >= 0 and lines[j].startswith('@['):
            j -= 1
        block = []
        while j >= 0 and lines[j].startswith('--'):
            block.append(lines[j])
            j -= 1
        block.reverse()
        yield kind, name, block, i + 1

def main():
    for root in sys.argv[1:]:
        tot = collections.Counter(); doc = collections.Counter()
        maint = collections.Counter(); anym = 0; nblocks = 0; doclines = 0; mlines = 0
        example_thms = 0
        for dp, _, fs in os.walk(root):
            for f in fs:
                if not f.endswith('.sw'):
                    continue
                for kind, name, block, ln in blocks(os.path.join(dp, f)):
                    if '%' in name:
                        continue
                    if kind == 'theorem' and name.endswith('Example'):
                        example_thms += 1
                        continue
                    tot[kind] += 1
                    if block:
                        doc[kind] += 1
                        nblocks += 1
                        doclines += len(block)
                        hit = False
                        for k, rx in MAINT.items():
                            if any(rx.search(b) for b in block):
                                maint[k] += 1; hit = True
                        mlines += sum(1 for b in block if any(rx.search(b) for rx in MAINT.values()))
                        anym += hit
        print(f'== {root}')
        for k in sorted(tot):
            print(f'  {k:9} {doc[k]:5} / {tot[k]:5}  ({100*doc[k]/tot[k]:.0f}%)')
        T = sum(tot.values()); D = sum(doc.values())
        print(f'  all       {D:5} / {T:5}  ({100*D/T:.0f}%)')
        print(f'  blocks {nblocks}, lines {doclines}; blocks with a maintainer marker {anym}: {dict(maint)}; marked lines {mlines}')
        print(f'  ...Example theorems (excluded above): {example_thms}')

main()
