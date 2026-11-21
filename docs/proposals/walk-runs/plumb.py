import json, re, collections
s = json.load(open(__import__('sys').argv[1]))
atom = re.compile(r"^[A-Za-z_][\w.']*( _)*$|^_$")
simple = re.compile(r"^\[[^\]]*\]$|^\([^()]*\)$")
head = re.compile(r"^\(?(Parse\.)?(runsBind|runsLook|runsMap|runsSame|runsFromBind|runsFromBindAt|runsBindEnd|runsLookEnd|runsPure|runsFromPure\w*|runsFromMark)\b")
thunk = re.compile(r"^\(\(\) => [^()]*(\([^()]*\))*[^()]*\)$")
cont = re.compile(r"^\(\w+ => .*\)\)*$")
join = re.compile(r"byComputing\)*$|appendNil.*flipped\)*$|^\(?List\.appendNil")
tot = collections.Counter(); pl = collections.Counter(); n = collections.Counter()
rows = []
for x in s:
    k = 'records' if x['kind'] not in ('Parse.Runs','Parse.RunsFrom','ItemReads') else x['kind']
    L = x['body'].split('\n'); p = 0
    for l in L:
        if (atom.match(l) and l != 'byComputing') or simple.match(l) or head.match(l) or thunk.match(l) or join.search(l) or (cont.match(l) and len(l) < 60):
            p += 1
    tot[k] += len(L); pl[k] += p; n[k] += 1
    rows.append((x['proof'], p, x['name']))
for k in tot: print(k, n[k], 'theorems', tot[k], 'lines', pl[k], 'plumbing-ish', round(100*pl[k]/tot[k]))
