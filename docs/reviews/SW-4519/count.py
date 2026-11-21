import sys, os, re, json
root = sys.argv[1]
RAW = len(sys.argv) > 3 and sys.argv[3] == '--raw'
out = []
def strip_str(l):
    l = re.sub(r'"(\\.|[^"\\])*"', '""', l)
    l = re.sub(r"'(\\.|[^'\\])'", "''", l)
    i = l.find('--')
    return l if i < 0 else l[:i]
for dp, dn, fn in os.walk(root):
    for f in fn:
        if not f.endswith('.sw'): continue
        p = os.path.join(dp, f)
        lines = open(p).read().split('\n')
        i = 0; n = len(lines)
        while i < n:
            l = lines[i]
            if l.startswith('theorem '):
                name = l.split()[1]
                depth = 0; j = i; stmt_end = None; tail = ''
                while j < n:
                    s = strip_str(lines[j])
                    k = 0
                    while k < len(s):
                        c = s[k]
                        if c in '([{': depth += 1
                        elif c in ')]}': depth -= 1
                        elif s.startswith(':=', k) and depth == 0:
                            stmt_end = j; tail = s[k+2:].strip(); break
                        k += 1
                    if stmt_end is not None: break
                    j += 1
                if stmt_end is None: i += 1; continue
                k = stmt_end + 1
                body = [tail] if tail else []
                while k < n and (lines[k].startswith(' ') or lines[k].strip() == ''):
                    if lines[k].strip() and not lines[k].strip().startswith('--'):
                        body.append(lines[k].rstrip() if RAW else lines[k].strip())
                    k += 1
                # trailing blank removal irrelevant
                out.append(dict(file=os.path.relpath(p, root), name=name, line=i+1,
                    stmt=stmt_end - i + 1, proof=len(body), body='\n'.join(body)))
                i = k
            else:
                i += 1
json.dump(out, open(sys.argv[2], 'w'))
print(len(out), sum(t['proof'] for t in out), sum(t['stmt'] for t in out))
