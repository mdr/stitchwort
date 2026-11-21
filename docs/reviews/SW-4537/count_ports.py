"""Count the ported theorems. usage: python3 count_ports.py <tools/fmt/src> sample.json File.lean File.v ...

A counted theorem follows a line `-- sample: name` (Lean) or `(* sample: name *)` (Rocq) and runs to the
next blank line. Statement: up to the line holding `:= by` or ending `:=` (Lean), or the line before
`Proof.` (Rocq). Proof: the rest, `Proof.` and `Qed.` lines included. Comment-only lines are not counted:
`--` lines in Lean only (in Rocq `--` is a bullet), `(* ... *)` lines in Rocq.
Prints one CSV row per theorem: lines and non-blank characters, statement and proof, in each system.
A counted port line over 100 columns (rule 12) is reported on stderr and makes the exit status 1.
A theorem listed twice in sample.json (homeStands: main draw and reserve) is printed once per main draw.
"""
import sys, json, re, collections
root, sample, files = sys.argv[1], json.load(open(sys.argv[2])), sys.argv[3:]
wide = []
chars = lambda ls: sum(len(re.sub(r'\s', '', l)) for l in ls)
def blocks(path):
    lean = path.endswith('.lean'); ls = open(path).read().split('\n'); out = {}
    for i, l in enumerate(ls):
        m = re.match(r'(?:--|\(\*) sample: (\S+)', l)
        if not m: continue
        j = i + 1; body = []
        while j < len(ls) and ls[j].strip():
            comment = r'\s*--' if lean else r'\s*\(\*.*\*\)$'
            if not re.match(comment, ls[j]):
                body.append(ls[j])
                if len(ls[j]) > 100: wide.append(f'{path}:{j + 1}: {len(ls[j])} columns')
            j += 1
        if lean: cut = next(k for k, b in enumerate(body) if ':= by' in b or b.rstrip().endswith(':=')) + 1
        else: cut = next(k for k, b in enumerate(body) if b.lstrip().startswith('Proof.'))
        out[m.group(1)] = (cut, len(body) - cut, chars(body[:cut]), chars(body[cut:]))
    return out
ports = collections.defaultdict(dict)
for f in files:
    for name, v in blocks(f).items(): ports[name]['lean' if f.endswith('.lean') else 'rocq'] = v
print('stratum,name,sw_stmt,sw_proof,sw_stmt_ch,sw_proof_ch,lean_stmt,lean_proof,lean_stmt_ch,lean_proof_ch,rocq_stmt,rocq_proof,rocq_stmt_ch,rocq_proof_ch,role')
seen = set()
for t in sample:
    if t['role'] != 'main' and t['name'] in seen: continue
    seen.add(t['name'])
    p = ports.get(t['name'].rstrip(':'))
    if not p or len(p) < 2: continue
    ls = open(root + '/' + t['file']).read().split('\n')
    a = t['line'] - 1; st = ls[a:a + t['stmt']]
    k = a + t['stmt']; pr = []
    while k < len(ls) and (ls[k].startswith(' ') or not ls[k].strip()):
        if ls[k].strip() and not ls[k].strip().startswith('--'): pr.append(ls[k])
        k += 1
    tail = st[-1].split(':=', 1)[1] if ':=' in st[-1] else ''   # a proof begun on the `:=` line
    print(','.join(map(str, [t['stratum'], t['name'].rstrip(':'), t['stmt'], t['proof'], chars(st) - chars([tail]),
                             chars(pr) + chars([tail]), *p['lean'], *p['rocq'], t['role']])))
for w in wide: print(w, file=sys.stderr)
sys.exit(1 if wide else 0)
