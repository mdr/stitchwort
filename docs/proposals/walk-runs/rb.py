import json, re, sys, collections
t = [x for x in json.load(open(sys.argv[1])) if '/Tests/' not in x['file']]
root = sys.argv[2]
cache = {}
sel = []
for x in t:
    if x['file'] not in cache: cache[x['file']] = open(root + '/' + x['file']).read().split('\n')
    st = ' '.join(cache[x['file']][x['line']-1:x['line']-1+x['stmt']])
    st = st[:st.rfind(':=')]
    i = st.rfind('):')
    concl = st[i+2:] if i >= 0 else st.split(':', 1)[-1]
    m = re.search(r'Parse\.RunsFrom|Parse\.Runs\b|\b[A-Z]\w*Reads\b', concl)
    if m:
        x['kind'] = m.group(0); x['concl'] = concl.strip(); sel.append(x)
print(len(sel), sum(x['proof'] for x in sel))
c = collections.Counter(); cl = collections.Counter()
for x in sel: c[x['kind']] += 1; cl[x['kind']] += x['proof']
print(c, cl)
files = collections.Counter()
for x in sel: files[x['file']] += x['proof']
for f, n in files.most_common(15): print(n, f)
L = [l for x in sel for l in x['body'].split('\n')]
atom = re.compile(r"^[A-Za-z_][\w.']*( _)*$|^_$")
simple = re.compile(r"^\[[^\]]*\]$|^\([^()]*\)$")
print('lines', len(L), 'lone', sum(1 for l in L if atom.match(l) and l not in ('byComputing',)), 'lone+simple', sum(1 for l in L if (atom.match(l) and l!='byComputing') or simple.match(l)))
for w in ['Parse.runsBind', 'runsLook', 'Parse.runsMap', 'runsSame', 'Parse.runsFromBind', 'Parse.runsPure', 'runsBindEnd', 'Parse.runsOneOf', 'match ', 'rewrite', 'appendAssoc', 'appendNil', 'byWalking', 'state starts honest']:
    print(w, sum(l.count(w) for l in L))
json.dump(sel, open(sys.argv[3], 'w'))
