#!/usr/bin/env python3
"""How many tests and `...Example` theorems attach to a declaration by name.
Usage: examples.py ROOT (from the repo root). Names are as written in the
source (std writes `def List.map`; a project file's namespace line is
prefixed)."""
import os, re, sys, collections

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(def|theorem|type|instance|ability|opaque def|opaque|interface)\s+([A-Za-z0-9_.\'%]+)')
TEST = re.compile(r'^test\s+"([^"]*)"')
NS = re.compile(r'^namespace\s+([A-Za-z0-9_.]+)')

root = sys.argv[1]
decls = {}          # full name -> kind
short = collections.defaultdict(set)   # (file, short) -> full
tests = []          # (file, ns, name)
examples = []       # (file, full name)
for dp, _, fs in os.walk(root):
    for f in fs:
        if not f.endswith('.sw'):
            continue
        p = os.path.join(dp, f)
        ns = ''
        for l in open(p, encoding='utf-8'):
            m = NS.match(l)
            if m:
                ns = m.group(1) + '.'
            m = DECL.match(l)
            if m:
                full = ns + m.group(2)
                decls[full] = m.group(1)
                if full.endswith('Example') or re.search(r'Example\d+$', full):
                    examples.append((p, full))
                short[(p, full.split('.')[-1])].add(full)
            m = TEST.match(l)
            if m:
                tests.append((p, ns, m.group(1)))

def resolve(p, ns, word):
    for cand in (word, ns + word):
        if cand in decls:
            return cand
    s = short.get((p, word))
    if s and len(s) == 1:
        return next(iter(s))
    return None

how = collections.Counter(); targets = collections.Counter(); samples = collections.defaultdict(list)
for p, ns, name in tests:
    if resolve(p, ns, name):
        k = 'exact'
    else:
        first = re.split(r'[ :,(]', name, maxsplit=1)[0]
        k = 'first word' if first != name and resolve(p, ns, first) else 'none'
    how[k] += 1
    if len(samples[k]) < 12:
        samples[k].append(name)
print(f'tests: {len(tests)}', dict(how))
for k, v in samples.items():
    print(f'  {k}: {v}')

eh = collections.Counter(); es = collections.defaultdict(list)
for p, full in examples:
    base = re.sub(r'Example\d*$', '', full)
    if base in decls:
        k = 'base is a ' + decls[base]
    else:
        k = 'no base'
    eh[k] += 1
    if len(es[k]) < 10:
        es[k].append(full)
print(f'Example theorems: {len(examples)}', dict(eh))
for k, v in es.items():
    print(f'  {k}: {v}')

# Proposed rule: exact name, or a qualified name (with a dot) then ' ', ',' or ':'.
rule = collections.Counter(); per = collections.Counter(); rs = collections.defaultdict(list)
for p, ns, name in tests:
    t = resolve(p, ns, name)
    if t:
        k = 'exact'
    else:
        m = re.match(r'([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_\']+)+)[ ,:]', name)
        t = resolve(p, ns, m.group(1)) if m else None
        k = 'qualified prefix' if t else 'none'
    rule[k] += 1
    if t: per[t] += 1
    if len(rs[k]) < 8: rs[k].append(name)
print('proposed rule:', dict(rule), 'distinct targets', len(per), 'max per target', per.most_common(3))
for k, v in rs.items():
    print(f'  {k}: {v}')
withex = set(t for t in per if decls.get(t) in ('def', 'opaque def', 'opaque'))
for p, full in examples:
    base = re.sub(r'Example\d*$', '', full)
    if decls.get(base) in ('def', 'opaque def', 'opaque'):
        withex.add(base)
ndefs = sum(1 for n, k in decls.items() if k in ('def', 'opaque def', 'opaque') and '%' not in n)
print(f'definitions with at least one attached example: {len(withex)} of {ndefs}')
for n in ('List.filterMap', 'Text.padLeft', 'Option.toList', 'List.allSome', 'Text.padRight'):
    print(n, n in decls, n in withex, [x for p, x in examples if x.startswith(n)])
